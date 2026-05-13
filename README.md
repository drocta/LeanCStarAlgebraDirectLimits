Work towards supporting direct limits of C^\*-algebras in lean4, and in particular UHF algebras, and quantum spin systems.  
This repository constructs direct limit instances for various star structures, as well as for `Norm`, `NormedAddGroup`, etc., and for `CStarRing`,
and does produce an instance for `CStarAlgebra` given a directed system of `CStarAlgebra`s, as the `Completion` of the `DirectLimit`.
This project is still under active development, and several of the parts will need to be updated before PRs based on them can be made, such as the way it handles the norm compatibility,
and adding the lift maps for the `CStarAlgebra`, etc. . In addition, not all of the improvements made during code review of the PRs have been copied back to this repository.
So far (as of May 11 2026), I've spun out the following requests for mathlib from code in here, which have been merged:   
 * [PR #38308 feat(Algebra/Colimit/DirectLimit): add star structures (Star, StarRing, etc.) on DirectLimit](https://github.com/leanprover-community/mathlib4/pull/38308) and  
 * [PR #38672 feat(Algebra/Colimit/DirectLimit): add Algebra structure for DirectLimit](https://github.com/leanprover-community/mathlib4/pull/38672)

# Roadmap

