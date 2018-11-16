# Coq formalization of static differentiation with static caching

## Installation

### Opam
```
wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin
```

### Opam Coq repository
```
opam repo add coq-released http://coq.inria.fr/opam/released
```

### Installing packages
```
opam install coq.8.7.2 coq-equations.1.0+8.7 && opam pin add coq 8.7.2
```

## Compilation

The following command runs the typechecking of the entire Coq development.

```
make
```

## Documentation

Running
```
make doc
```
produces a file ``doc/html/index.html`` which provides an overview of the development
as well as the mapping between the paper and the Coq development.

## Axioms

We are using two axioms:
```
Axiom fun_extensionality:
  forall (A B: Type) (f g: A -> B),
  (forall x, f x = g x) -> f = g.

Axiom prop_extensionality:
  forall (P Q: Prop), (P <-> Q) -> P = Q.
```

