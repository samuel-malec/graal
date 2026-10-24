package com.oracle.graal.pointsto.export;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Supplier;
import java.util.regex.Pattern;

import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.export.FlowReader.Held;
import com.oracle.graal.pointsto.export.FlowReader.Source;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.typestate.TypeState;

/**
 * Why an object is shared, kept when asked to ({@code -Dsideeffects.explainSharing=<regex of type names>}):
 * how it was reached and from which shared object. Diagnostics only: nothing here changes the answer.
 */
final class SharingExplanation {

    /**
     * Why an object is shared, kept when asked to explain ({@code -Dsideeffects.explainSharing=<regex
     * of type names>}): how it was reached and from which shared object.
     */
    record Cause(String how, AnalysisObject from, List<TypeFlow<?>> via) {
    }

    private final PointsToAnalysis bb;
    private final AnalysisUniverse universe;
    private final Pattern explain;
    private final Set<AnalysisObject> known;
    private final Set<AnalysisObject> shared;
    private final Set<AnalysisObject> contents;
    StoredPlaces places;

    /** For the explanation: the stores into arrays of a value the analysis can't name. */
    final List<String> arrayStoresOfAny = new ArrayList<>();

    final Map<AnalysisObject, Cause> causes = new HashMap<>();
    final Map<AnalysisType, AnalysisObject> anyOfFrom = new HashMap<>();
    final Map<AnalysisType, String> anyOfHow = new HashMap<>();

    /** The reason the objects shared next are shared for: set by whoever shares them. */
    private Supplier<String> how = () -> "?";

    private AnalysisObject from;
    private List<TypeFlow<?>> via = List.of();

    SharingExplanation(ThreadEscape escape) {
        this.bb = escape.bb;
        this.universe = escape.universe;
        this.explain = escape.explain;
        this.known = escape.known;
        this.shared = escape.shared;
        this.contents = escape.contents;
    }

    void connect(StoredPlaces places) {
        this.places = places;
    }

    void because(Supplier<String> reason, AnalysisObject source) {
        because(reason, source, List.of());
    }

    void because(Supplier<String> reason, AnalysisObject source, List<TypeFlow<?>> flows) {
        if (explain != null) {
            how = reason;
            from = source;
            via = flows;
        }
    }

    String summary(Held held) {
        return "(" + held.states().size() + " states, any " + held.any().stream().map(AnalysisType::toJavaName).toList() + ", from " +
                        held.stored().stream().map(this::describeStored).toList() + ")";
    }

    String describe(Held held) {
        StringBuilder text = new StringBuilder();
        int shown = 0;
        for (AnalysisObject object : held.objectsIn(bb)) {
            if (shown++ < 4) {
                text.append(GraphExport.PointsTo.objectName(object)).append(", ");
            }
        }
        return text + (shown > 4 ? "and " + (shown - 4) + " more" : "") + held.any().stream().map(type -> " any " + type.toJavaName()).toList();
    }

    /** For the explanation: what is stored into what, from the store the sharing started at to the object. */
    List<Source> storedPath() {
        List<Source> path = new ArrayList<>();
        for (Source at = places.currentSource; at != null && path.size() < 20; at = places.sourceParent.get(at)) {
            path.add(0, at);
        }
        return path;
    }

    String describeStored(Source stored) {
        return describeStored(stored.key()) + (stored.filters().isEmpty() ? "" : " as " + stored.filters().stream().map(AnalysisType::toJavaName).toList());
    }

    String describeStored(Object stored) {
        if (stored == FlowReader.ARRAYS) {
            return "any array";
        } else if (stored instanceof AnalysisField field) {
            return "field " + field.format("%H.%n");
        } else if (stored instanceof TypeFlow<?> flow) {
            return "flow " + flow.getClass().getSimpleName() + (flow.getSource() instanceof jdk.vm.ci.code.BytecodePosition position ? " at " + GraphExport.PointsTo.site(position) : "");
        }
        return String.valueOf(stored);
    }

    /**
     * How the analysis has an object reach a flow, from where it is made: the flows between, walking
     * back along the inputs the analysis recorded ({@code -H:+TrackInputFlows}).
     */
    private List<String> flowPath(List<TypeFlow<?>> starts, AnalysisObject object) {
        Map<TypeFlow<?>, TypeFlow<?>> next = new IdentityHashMap<>();
        Deque<TypeFlow<?>> queue = new ArrayDeque<>();
        for (TypeFlow<?> start : starts) {
            if (start != null && holds(start, object) && next.putIfAbsent(start, start) == null) {
                queue.add(start);
            }
        }
        TypeFlow<?> end = null;
        while (!queue.isEmpty() && end == null) {
            TypeFlow<?> flow = queue.poll();
            boolean extended = false;
            for (TypeFlow<?> input : flow.getInputs()) {
                if (holds(input, object) && next.putIfAbsent(input, flow) == null) {
                    queue.add(input);
                    extended = true;
                }
            }
            if (!extended && flow.getInputs().isEmpty()) {
                end = flow;
            }
        }
        List<String> path = new ArrayList<>();
        if (end == null) {
            return path;
        }
        // The walk went back from the value to where the object is made; print it the way the object travels.
        for (TypeFlow<?> flow = end; path.size() < 40; flow = next.get(flow)) {
            String source = flow.getSource() instanceof jdk.vm.ci.code.BytecodePosition position ? " at " + GraphExport.PointsTo.site(position) : "";
            path.add(flow.getClass().getSimpleName() + source + (flow.isSaturated() ? " (saturated)" : ""));
            if (next.get(flow) == flow) {
                break;
            }
        }
        return path;
    }

    /** Whether the flow may hold the object: it does if it saturated, as far as one can tell. */
    private boolean holds(TypeFlow<?> flow, AnalysisObject object) {
        if (flow.isSaturated()) {
            return flow.getDeclaredType() == null || flow.getDeclaredType().isAssignableFrom(object.type());
        }
        TypeState state = flow.getOutputState(bb);
        if (state == null || state.isPrimitive()) {
            return false;
        }
        for (AnalysisObject held : state.objects(bb)) {
            // The same object, or one of its type: a flow may name the object by its type alone.
            if (held == object || held.type().equals(object.type())) {
                return true;
            }
        }
        return false;
    }

    /** An object is shared for the reason last given to {@link #because}. */
    void recordCause(AnalysisObject object) {
        causes.put(object, new Cause(how.get(), from, via));
    }

    /** Any object of a type is shared, or has shared contents, for the reason last given. */
    void recordAnyOf(AnalysisType type) {
        anyOfFrom.put(type, from);
        anyOfHow.put(type, how.get());
    }

    /** An object is shared: the cause, and for the types the pattern names, the chain of stored places it went through. */
    void recordShared(AnalysisObject object) {
        recordCause(object);
        if (explain.matcher(GraphExport.PointsTo.objectName(object)).find() && object.isContextInsensitiveObject()) {
            StringBuilder trace = new StringBuilder("THREADESCAPE shared " + GraphExport.PointsTo.objectName(object) + " by " + how.get());
            StackTraceElement[] frames = new Throwable().getStackTrace();
            for (int i = 2; i < Math.min(frames.length, 5); i++) {
                trace.append("\n    at ").append(frames[i].getMethodName()).append(":").append(frames[i].getLineNumber());
            }
            storedPath().forEach(stored -> trace.append("\n    through ").append(describeStored(stored)));
            System.err.println(trace);
        }
    }

    /** Prints how the root methods were registered, the callers the analysis cannot see. */
    private void printRootMethods() {
        Map<String, Integer> rootMethods = new TreeMap<>();
        for (AnalysisMethod method : universe.getMethods()) {
            if (ThreadEscape.analysed(method) && (method.isDirectRootMethod() || method.isVirtualRootMethod())) {
                String owner = method.getDeclaringClass().toJavaName(true);
                owner = owner.replaceAll("\\$Proxy/s[0-9a-f]+", "\\$Proxy").replaceAll("\\.proxy[0-9]+\\.", ".proxyN.");
                Object reason = method.getRootReason();
                String why = String.valueOf(reason).replaceAll("\\$Proxy/s[0-9a-f]+", "\\$Proxy").replaceAll("[0-9a-f]{6,}", "#");
                rootMethods.merge((method.isDirectRootMethod() ? "direct " : "virtual ") + owner + "." + method.getName() + " <- " + (why.length() > 150 ? why.substring(0, 150) : why), 1, Integer::sum);
            }
        }
        System.err.println("THREADESCAPE " + rootMethods.values().stream().mapToInt(Integer::intValue).sum() + " root methods:");
        rootMethods.entrySet().stream().limit(5000).forEach(e -> System.err.println("THREADESCAPE   root " + e.getValue() + "  " + e.getKey()));
    }

    /** Prints, for the types the pattern names, a few chains of reasons and how the shared objects divide by the reason at the root of their chain. */
    void explainSharing() {
        Map<String, Integer> roots = new TreeMap<>();
        Map<String, Integer> printed = new HashMap<>();
        for (AnalysisObject object : shared) {
            Cause cause = causes.get(object);
            while (cause != null && cause.from() != null) {
                cause = causes.get(cause.from());
            }
            String root = cause == null ? "?" : cause.how().replaceAll("^(any [^ ]+) .*", "$1").replaceAll("^(argument of a call in |result of a call in )[^ ]* (to [^ ]*).*", "$1$2");
            roots.merge(root.length() > 90 ? root.substring(0, 90) : root, 1, Integer::sum);
        }
        System.err.println("THREADESCAPE shared " + shared.size() + " and with shared contents " + contents.size() + " of " + known.size() + " known objects; by the reason at the root of the chain:");
        roots.entrySet().stream().sorted((a, b) -> b.getValue() - a.getValue()).limit(25).forEach(e -> System.err.println("THREADESCAPE   " + e.getValue() + "  " + e.getKey()));
        printRootMethods();
        System.err.println("THREADESCAPE " + arrayStoresOfAny.size() + " stores into arrays of a value that saturated:");
        arrayStoresOfAny.stream().sorted().limit(60).forEach(line -> System.err.println("THREADESCAPE   " + line));
        for (AnalysisObject object : new TreeSet<>(contents)) {
            String name = GraphExport.PointsTo.objectName(object);
            if (explain.matcher(name).find() && printed.merge("all", 1, Integer::sum) <= 8) {
                StringBuilder chain = new StringBuilder(GraphExport.PointsTo.objectName(object) + (shared.contains(object) ? "" : " (contents only)"));
                AnalysisObject at = object;
                for (int depth = 0; depth < 30; depth++) {
                    Cause cause = causes.get(at);
                    if (cause == null) {
                        break;
                    }
                    chain.append("\n    <- ").append(cause.how());
                    if (!cause.via().isEmpty()) {
                        flowPath(cause.via(), at).forEach(step -> chain.append("\n         flows ").append(step));
                    }
                    if (cause.from() == null) {
                        break;
                    }
                    at = cause.from();
                    chain.append("\n    <- ").append(GraphExport.PointsTo.objectName(at));
                }
                System.err.println("THREADESCAPE " + chain);
            }
        }
    }
}
