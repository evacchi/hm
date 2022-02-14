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
import static io.github.evacchi.example.Type.TypeVariable;
import static io.github.evacchi.example.Type.TypedEnv;
import static io.github.evacchi.example.Type.mgu;
import static java.util.Map.entry;
import static java.util.stream.Collectors.joining;
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
    List<TypeVariable> freeVars();
    final class TypeVariable implements Type {
        private static int next = 0;
        String v; TypeVariable(String v) { this.v =v ; }
        public List<TypeVariable> freeVars() { return new ArrayList<>(List.of(this)); }

        public String toString() { return v; }
        public boolean equals(Object o) { return o instanceof TypeVariable tv && Objects.equals(v, tv.v); }
        public int hashCode() { return Objects.hash(v); }
    }
    static TypeVariable TypeVariable(String v) {return new TypeVariable(v);}
    static TypeVariable TypeVariable() { return new TypeVariable("a" + TypeVariable.next++); }

    record Arrow(Type from, Type to) implements Type {
        public List<TypeVariable> freeVars() { return Stream.concat(from.freeVars().stream(), to.freeVars().stream()).collect(toList()); }
        public String toString() { return String.format("(%s->%s)", from, to); }}
    static Arrow Arrow(Type t1, Type t2) { return new Arrow(t1,t2); }

    record TypeCons(String name, List<Type> types) implements Type {
        public String toString() {
            return name + (types.isEmpty() ? "" : types.stream().map(Objects::toString).collect(joining(",", "<", ">"))); }
        public List<TypeVariable> freeVars() { return types.stream().flatMap(tp -> tp.freeVars().stream()).collect(toList()); }
    }
    static TypeCons TypeCons(String name, List<Type> types) { return new TypeCons(name, types); }

    abstract class Subst {
        static Subst Empty = new Subst() { Type lookup(TypeVariable tv) { return tv; } };
        abstract Type lookup(TypeVariable tv);
        Type apply(Type t) {
            return switch(t) {
                case TypeVariable tv -> {
                    var u = lookup(tv);
                    yield (t.equals(u)) ? t : apply(u);
                }
                case Arrow a -> Arrow(apply(a.from()), apply(a.to()));
                case TypeCons tc -> TypeCons(tc.name(), tc.types().stream().map(this::apply).toList());
            };
        }
        Subst extend(TypeVariable x, Type t) {
            return new Subst() {
                @Override Type lookup(TypeVariable y) { return (x.equals(y))? t : Subst.this.lookup(y); }
            };
        }
    }

    record TypeScheme(List<TypeVariable> typeVars, Type type) {
        // returns the type of the scheme after all universally quantified
        // type vars have been renamed to fresh vars
        public Type newInstance() {
            var subst = Subst.Empty;
            for (TypeVariable tv : typeVars) {
                subst = subst.extend(tv, TypeVariable());
            }
            return subst.apply(type);
        }
        public List<TypeVariable> freeVars() {
            var tv = this.type().freeVars();
            tv.removeAll(this.typeVars());
            return tv;
        }
    }
    static TypeScheme TypeScheme(List<TypeVariable> typeVars, Type t) { return new TypeScheme(typeVars, t); }

    final class Env {
        private Map<String, TypeScheme> env;
        public Env() {
            this(new HashMap<>());
        }
        public Env(Map<String, TypeScheme> env) {
            this.env = env;
        }
        TypeScheme lookup(String name) { return env.get(name); }
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

        List<TypeVariable> freeVars() {
            return env.values().stream()
                    .flatMap(ts -> ts.freeVars().stream())
                    .collect(toList());
        }
    }

    class TypedEnv {
        Env env;

        public TypedEnv(Env env) {
            this.env = env;
        }

        Type typeOf(Term e) {
            var a = TypeVariable();
            return tp(e, a, Subst.Empty).apply(a);
        }

        Subst tp(Term e, Type t, Subst s) {
            return switch (e) {
                case Var v -> {
                    var u = env.lookup(v.name());
                    if (u == null) throw new RuntimeException("undefined: " + v.name());
                    else yield mgu(u.newInstance(), t, s);
                }
                case Lambda l -> {
                    var a = TypeVariable();
                    var b = TypeVariable();
                    var s1 = mgu(t, Arrow(a, b), s);
                    var env1 = env.append(l.v(), TypeScheme(List.of(), a));
                    yield new TypedEnv(env1).tp(l.body(), b, s1);
                }
                case Apply app -> {
                    var a = TypeVariable();
                    var s1 = this.tp(app.fn(), Arrow(a, t), s);
                    yield this.tp(app.arg(), a, s1);
                }
                case Let l -> {
                    var a = TypeVariable();
                    var s1 = this.tp(l.defn(), Arrow(a, t), s);
                    yield new TypedEnv( env.append(l.v(), env.apply(s1).toTypeScheme(s1.apply(a))) ).tp(l.body(), t, s1);
                }
                case LetRec l -> {
                    var a = TypeVariable();
                    var b = TypeVariable();
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
     */
    static Subst mgu(Type t, Type u, Subst s) {
        Type st = s.apply(t);
        Type su = s.apply(u);
        if (st instanceof TypeVariable a && su instanceof TypeVariable b && a.equals(b)) {
            return s;
        }
        if (st instanceof TypeVariable a && !(su.freeVars().contains(st))) {
            return s.extend(a, su);
        }
        if (/*    st instanceof any   */      su instanceof TypeVariable) {
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
    TypeCons booleanType = TypeCons("Boolean", List.of());
    TypeCons intType = TypeCons("Int", List.of());
    static TypeCons listType(Type t) { return TypeCons("List", List.of(t)); }
    static TypeScheme gen(Type t) { return TypeScheme(t.freeVars(), t); } // /*new Env().toTypeScheme(t)*/ }

    TypeVariable a = TypeVariable();
    Env env = new Env(Map.ofEntries(
        entry("true", gen(booleanType)),
        entry("false", gen(booleanType)),
        entry("if", gen(Arrow(booleanType, Arrow(a, Arrow(a, a))))),
        entry("zero", gen(intType)),
        entry("succ", gen(Arrow(intType, intType))),
        entry("nil", gen(listType(a))),
        entry("cons", gen(Arrow(a, Arrow(listType(a), listType(a))))),
        entry("isEmpty", gen(Arrow(listType(a), booleanType))),
        entry("head", gen(Arrow(listType(a), a))),
        entry("tail", gen(Arrow(listType(a), listType(a)))),
        entry("fix", gen(Arrow(Arrow(a, a), a)))
    ));

    static String showType(Term e) {
        return new TypedEnv(env).typeOf(e).toString();
    }

    public static void main(String[] args) {
        System.out.println(showType(Lambda("x", Apply(Apply(Var("cons"), Var("x")), Var("nil")))));
    }

}

