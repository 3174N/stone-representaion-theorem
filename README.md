# Stone Representation Theorem

This repository contains a formalization of [Stone's Representation Theorem](https://en.wikipedia.org/wiki/Stone's_representation_theorem_for_Boolean_algebras) using Lean4.

## File Overview
The lean files are located in the `Stone/` directory.

- `Defs.lean` - Contains the base definitions and instances for the project. 2 as a boolean algebra, Hom(A,2) as a stone space, etc. Also containes some basic lemmas regarding these definitions.
- `ExistsMaximalIdeal.lean` - Containes a lemma useful for the next lemma.
- `ExistsNonZeroHomomorphism.lean` - Contains a lemma useful for the final isomorphism.
- `StoneCounit.lean` - Contains the counit isomorphism required for the definition of the Stone Duality.
- `StoneEquivalence.lean` - Contains the definition of the Stone Duality.
- `StoneUnit.lean` - Contains the unit isomorphism required for the definition of the Stone Duality.
