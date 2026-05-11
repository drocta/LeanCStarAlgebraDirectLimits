Work towards supporting direct limits of C^\*-algebras in lean4, and in particular UHF algebras, and quantum spin systems.  
This repository constructs direct limit instances for various star structures, as well as for `Norm`, `NormedAddGroup`, etc., and for `CStarRing`,
and does produce an instance for `CStarAlgebra` given a directed system of `CStarAlgebra`s, as the `Completion` of the `DirectLimit`.
However, there is still work to be done. For example, the way it handles the norm compatibility needs improvement,  
and it doesn't have the lift maps for the `CStarAlgebra` yet.
So far (as of May 11 2026), I've spun out two pull requests for mathlib from code in here, which have been merged,  
namely, [PR #38308 feat(Algebra/Colimit/DirectLimit): add star structures (Star, StarRing, etc.) on DirectLimit](https://github.com/leanprover-community/mathlib4/pull/38308) and  
[PR #38672 feat(Algebra/Colimit/DirectLimit): add Algebra structure for DirectLimit](https://github.com/leanprover-community/mathlib4/pull/38672)
