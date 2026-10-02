public class Demo {

    private static class A {
        int value;

        public A(int value) {
            this.value = value;
        }
    }

    private static class B {
        A first;
        A second;
    }

    public static void main(String[] args) {
        B b = new B();
        A a = new A(10);
        b.first = a;
        b.second = a;
        a = new A(15);
        System.out.println(b.first.value);
        System.out.println(b.second.value);
    }
}
