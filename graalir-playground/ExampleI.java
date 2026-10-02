public class ExampleI {
    static class Counter {
        int value;
    }

    static class Config {
        int limit;
    }

    static void bump(Counter counter) {
        counter.value++;
    }

    static void process(Counter counter, Config config, int n) {
        for (int i = 0; i < n; i++) {
            bump(counter);
            if (i > config.limit) {
                break;
            }
        }
    }

    public static void main(String[] args) {
        Config config = new Config();
        Counter counter = new Counter();
        config.limit = 10;
        process(counter, config, 10);
        System.out.println(counter.value);
    }
}
