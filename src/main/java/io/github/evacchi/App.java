package io.github.evacchi;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static io.github.evacchi.Term.*;
import static io.github.evacchi.Type.*;
import static io.github.evacchi.TypeSystem.*;

sealed interface Term {
    record Lambda(String v, Term body) implements Term {}
    static Lambda Lambda(String v, Term body) { return new Lambda(v, body);}

    record Id(String name) implements Term {}
    static Id Id(String name) { return new Id(name); }

    record Apply(Term fn, Term arg) implements Term {}
    static Apply Apply(Term fn, Term arg) { return new Apply(fn, arg); }

    record Let(String v, Term defn, Term body) implements Term {}
    static Let Let(String v, Term defn, Term body) { return new Let(v, defn, body); }

    record LetRec(String v, Term defn, Term body) implements Term {}
    static LetRec LetRec(String v, Term defn, Term body) { return new LetRec(v, defn, body); }

}


interface App {
    public static void main(String[] args) {
        var ex = Lambda("n",
                Apply(Apply(Apply(Term.Id("if"),
                                        Apply(Term.Id("zero"), Id("n"))),
                                Id("1")),
                        Apply(Id("prev"), Id("n"))));


        var var1 = TypeVariable();
        Map<String, Type> env = Map.of(
                "true", BOOLEAN,
                "false", BOOLEAN,
                "if", Function(BOOLEAN, Function(var1, Function(var1, var1))),
                "prev", Function(INTEGER, INTEGER),
                "zero", Function(INTEGER, BOOLEAN),
                "times", Function(INTEGER, Function(INTEGER, INTEGER))
        );

        List.of(
                Id("5"),              // 5 : int
                Lambda("n", Id("5")), // n -> 5 : a->int
                Lambda("n", Lambda("m", Id("5"))), // n -> m -> 5 : a->b->int
                Let("dec", Lambda("n", Apply(Id("prev"), Id("n"))), // fun dec(n) = n - 1; dec(1)
                        Apply(Id("dec"), Id("1"))),
                LetRec("factorial",   // fun factorial(n) = if zero(n) 1 else n * factorial(n-1): int
                        Lambda("n",
                                Apply(Apply(Apply(Id("if"),
                                                        Apply(Id("zero"),Id("n"))),
                                                Id("1")),
                                        Apply(Apply(Id("times"),Id("n")),Apply(Id("prev"),Id("n"))))),
                        Apply(Id("factorial"), Id("5")))
        ).forEach(it -> {
            System.out.println(prune(analyse(it, env, Set.of())));
        });


    }
}