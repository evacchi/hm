package io.github.evacchi.example;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Stream;

import static io.github.evacchi.example.Term.Apply;
import static io.github.evacchi.example.Term.Lambda;
import static io.github.evacchi.example.Term.Let;
import static io.github.evacchi.example.Term.LetRec;
import static io.github.evacchi.example.Term.Var;
import static io.github.evacchi.example.Type.Arrow;
import static io.github.evacchi.example.Type.Env;
import static io.github.evacchi.example.Type.TypeCons;
import static io.github.evacchi.example.Type.TypeScheme;
import static io.github.evacchi.example.Type.TypeVar;
import static io.github.evacchi.example.Type.TypedEnv;
import static io.github.evacchi.example.Type.mgu;
import static java.util.Map.entry;
import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.reducing;
import static java.util.stream.Collectors.toList;


sealed interface Term {
    record Lambda(String v, Term body) implements Term { public String toString() { return String.format("(λ%s.%s)", v, body); } }
    static Lambda Lambda(String v, Term body) { return new Lambda(v, body);}

    record Var(String name) implements Term { public String toString() { return name; } }
    static Var Var(String name) { return new Var(name); }

    record Apply(Term fn, Term arg) implements Term { public String toString() { return String.format("(%s %s)", fn, arg); } }
    static Apply Apply(Term fn, Term arg) { return new Apply(fn, arg); }

    record Let(String v, Term defn, Term body) implements Term { public String toString() { return String.format("let %s = %s in %s", v, defn, body); } }
    static Let Let(String v, Term defn, Term body) { return new Let(v, defn, body); }

    record LetRec(String v, Term defn, Term body) implements Term { public String toString() { return String.format("letrec %s = %s in %s", v, defn, body); } }
    static LetRec LetRec(String v, Term defn, Term body) { return new LetRec(v, defn, body); }
}

sealed interface Type {
    List<TypeVar> freeVars();
    final class TypeVar implements Type {
        private static int next = 0;
        String v; TypeVar(String v) { this.v =v ; }
        public List<TypeVar> freeVars() { return new ArrayList<>(List.of(this)); }

        public String toString() { return v; }
        public boolean equals(Object o) { return o instanceof TypeVar tv && Objects.equals(v, tv.v); }
        public int hashCode() { return Objects.hash(v); }
    }
    static TypeVar TypeVar(String v) {return new TypeVar(v);}
    static TypeVar TypeVar() { return new TypeVar("a" + TypeVar.next++); }

    record Arrow(Type from, Type to) implements Type {
        public List<TypeVar> freeVars() { return Stream.concat(from.freeVars().stream(), to.freeVars().stream()).distinct().collect(toList()); }
        public String toString() { return String.format("(%s->%s)", from, to); }}
    static Arrow Arrow(Type t1, Type t2) { return new Arrow(t1,t2); }

    record TypeCons(String name, List<Type> types) implements Type {
        public String toString() {
            return name + (types.isEmpty() ? "" : types.stream().map(Objects::toString).collect(joining(",", "<", ">"))); }
        public List<TypeVar> freeVars() { return types.stream().flatMap(tp -> tp.freeVars().stream()).collect(toList()); }
    }
    static TypeCons TypeCons(String name, List<Type> types) { return new TypeCons(name, types); }

    /**
     * A substitution is an idempotent function from type variables to types.
     * It maps a finite number of type variables to some types, and leaves all other type variables unchanged.
     * The meaning of a substitution is extended point-wise to a mapping from types to types ({@link #apply(Type)})
     */
    abstract class Subst {
        static Subst Empty = new Subst() { Type lookup(TypeVar tv) { return tv; } };
        abstract Type lookup(TypeVar tv);
        Type apply(Type t) {
            return switch(t) {
                case TypeVar tv -> {
                    var u = lookup(tv);
                    yield (t.equals(u)) ? t : apply(u);
                }
                case Arrow a -> Arrow(apply(a.from()), apply(a.to()));
                case TypeCons tc -> TypeCons(tc.name(), tc.types().stream().map(this::apply).toList());
            };
        }
        Subst extend(TypeVar x, Type t) {
            return new Subst() {
                @Override Type lookup(TypeVar y) { return (x.equals(y))? t : Subst.this.lookup(y); }
            };
        }
    }

    /**
     * type schemes consist of a type and a list of names of type variables
     * which appear universally quantified in the type scheme.
     *
     * For instance, the type scheme ∀a∀b.a→b would be represented in the type checker as:
     * TypeScheme(List(TypeVar("a"), TypeVar("b")), Arrow(TypeVar("a"), TypeVar("b"))) .
     */
    record TypeScheme(List<TypeVar> typeVars, Type type) {
        // returns the type of the scheme after all universally quantified
        // type vars have been renamed to fresh vars
        public Type newInstance() {
            var subst = Subst.Empty;
            for (TypeVar tv : typeVars) {
                subst = subst.extend(tv, TypeVar());
            }
            return subst.apply(type);
        }
        public List<TypeVar> freeVars() {
            var tv = this.type().freeVars();
            tv.removeAll(this.typeVars());
            return tv;
        }
    }
    static TypeScheme TypeScheme(List<TypeVar> typeVars, Type t) { return new TypeScheme(typeVars, t); }

    class Env {
        private Map<String, TypeScheme> env;
        public Env(Map<String, TypeScheme> env) {
            this.env = env;
        }
        TypeScheme lookup(String name) { return env.get(name); }
        // The gen function turns a given type into a type scheme, quantifying over all type
        // variables that are free in the type, but not in the environment.
        TypeScheme toTypeScheme(Type t) {
            var res = t.freeVars();
            res.removeAll(this.freeVars());
            return TypeScheme(res, t);
        }
        Env apply(Subst subst) {
            var newEnv = new HashMap<String, TypeScheme>();
            for (var kv : env.entrySet()) {
                var ts = kv.getValue();
                var name = kv.getKey();
                Type substApplied = subst.apply(ts.type());
                newEnv.put(name, TypeScheme(ts.typeVars(), substApplied));
            }
            return new Env(newEnv);
        }

        Env append(String k, TypeScheme ts) {
            var e = new Env(new HashMap<>(env));
            e.env.put(k, ts);
            return e;
        }

        List<TypeVar> freeVars() {
            return env.values().stream()
                    .flatMap(ts -> ts.freeVars().stream())
                    .distinct()
                    .collect(toList());
        }
    }

    class TypedEnv {
        Env env;

        public TypedEnv(Env env) {
            this.env = env;
        }

        Type typeOf(Term e) {
            var a = TypeVar();
            var subst = tp(e, a, Subst.Empty);
            return subst.apply(a);
        }

        // This function takes as parameters an environment env (this),
        // a term e,
        // a proto-type t,
        // and a pre-existing substitution s
        //
        // The function yields a substitution s′ that extends s and that turns s′(env) ⊢ e : s′(t)
        // into a derivable type judgment according to the derivation rules of HM
        Subst tp(Term e, Type t, Subst s) {
            return switch (e) {
                case Var v -> {
                    var u = env.lookup(v.name());
                    if (u == null) throw new RuntimeException("undefined: " + v.name());
                    else yield mgu(u.newInstance(), t, s);
                }
                case Lambda l -> {
                    var a = TypeVar();
                    var b = TypeVar();
                    var s1 = mgu(t, Arrow(a, b), s);
                    var env1 = env.append(l.v(), TypeScheme(List.of(), a));
                    yield new TypedEnv(env1).tp(l.body(), b, s1);
                }
                case Apply app -> {
                    var a = TypeVar();
                    var s1 = this.tp(app.fn(), Arrow(a, t), s);
                    yield this.tp(app.arg(), a, s1);
                }
                case Let l -> {
                    var a = TypeVar();
                    var s1 = this.tp(l.defn(), Arrow(a, t), s);
                    yield new TypedEnv( env.append(l.v(), env.apply(s1).toTypeScheme(s1.apply(a))) ).tp(l.body(), t, s1);
                }
                case LetRec l -> {
                    var a = TypeVar();
                    var b = TypeVar();
                    var s1 = new TypedEnv( env.append(l.v(), TypeScheme(List.of(), a)) ).tp(l.defn(), b, s);
                    var s2 = mgu(a, b, s1);
                    var tenv = new TypedEnv(env.append(l.v(), env.apply(s2).toTypeScheme(s2.apply(a))));
                    yield tenv.tp(l.body(), t, s2);
                }
            };
        }
    }

    /**
     * most general unifier
     *
     * computes a substitution to make two given types equal (i.e. a unifier)
     */
    static Subst mgu(Type t, Type u, Subst s) {
        Type st = s.apply(t);
        Type su = s.apply(u);
        if (st instanceof TypeVar a && su instanceof TypeVar b && a.equals(b)) {
            return s;
        }
        if (st instanceof TypeVar a && !(su.freeVars().contains(st))) {
            return s.extend(a, su);
        }
        if (/*    st instanceof any   */      su instanceof TypeVar) {
            return mgu(u, t, s);
        }
        if (st instanceof Arrow a && su instanceof Arrow b) {
            return mgu(a.from(), b.from(), mgu(a.to(), b.to(), s));
        }
        if (st instanceof TypeCons a && su instanceof TypeCons b && a.name().equals(b.name())) {
            for (int i = 0; i < a.types().size(); i++) {
                 s = mgu(a.types().get(i), b.types().get(i), s);
            }
            return s;
        }
        throw new RuntimeException("cannot unify " + st + " with " + su);
    }

}

interface Predef {
    static TypeCons   BoolT = TypeCons("Boolean", List.of());
    static TypeCons   IntT = TypeCons("Int", List.of());
    static TypeCons   ListT(Type t) { return TypeCons("List", List.of(t)); }
    static TypeScheme gen(Type t) { return TypeScheme(t.freeVars(), t); } // /*new Env().toTypeScheme(t)*/ }

    TypeVar a = Type.TypeVar();
    Env env = new Env(Map.ofEntries(
        entry("true",    gen(BoolT)),
        entry("false",   gen(BoolT)),
        entry("if",      gen(Arrow(BoolT, Arrow(a, Arrow(a, a))))),
        entry("zero",    gen(IntT)),
        entry("succ",    gen(Arrow(IntT, IntT))),
        entry("nil",     gen(ListT(a))),
        entry("cons",    gen(Arrow(a, Arrow(ListT(a), ListT(a))))),
        entry("isEmpty", gen(Arrow(ListT(a), BoolT))),
        entry("head",    gen(Arrow(ListT(a), a))),
        entry("tail",    gen(Arrow(ListT(a), ListT(a)))),
        entry("fix",     gen(Arrow(Arrow(a, a), a)))
    ));

    static String showType(Term e) {
        return new TypedEnv(env).typeOf(e).toString();
    }

    public static void main(String[] args) {
        System.out.println(showType(Lambda("x", Apply(Apply(Var("cons"), Var("x")), Var("nil")))));
    }

}

