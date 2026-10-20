package concurrency;

/**
 * Control: a store, a release, and a store that overwrites the first. Without
 * the release the first store would be dead, as in deadstores.Adjacent. But
 * another thread that reads the flag as true must then see the 1, so the
 * release reads Counter.value, and the first store must stay.
 */
public class DeadStoreAcrossReleaseKeeps {

    static class Counter { int value; }

    static volatile boolean ready;

    static void demo(Counter counter) {
        counter.value = 1;
        ready = true;
        counter.value = 2;
    }

    public static void main(String[] args) {
        demo(new Counter());
    }
}
