# pyPDR

## Techniques I used

- one-context-for-all-frame solver (good to re-use the solving context)
- on-demand logic cone extraction (partially implemented)
- ctgDown / Down in MIC
- ternary simulation - for predecessor aggresive generalization (not suitable for python implementation)
- robust sanity checker
- rich console output for logging and monitoring
- cube and frame management system (add, join, push, etc.)
- unsat core extraction for inductive generalization and predecessor generalization
- infinite mic attempt (suggestion from arbrad)
- literals ordering according to their appearance in the trace (frequency), both in predecessor generalization (ternary sim) and inductive generalization (mic)

## Techniques I haven't tried - but should

- dynamically load the transition relation in solver
- reset solver with some frequency (keep the loaded logic relatively small)
- every time check assumption, some part (such as tr, should not be loaded every time, rather than push it to the solver at the beginning)
- use kissat or some SOTA SAT solver rather than z3
- use graceful strategy for propagating phase when solving the SAT problem
- backward ic3
- frame extending for solving SAT problem faster (mentioned in IC3, PDR and friends)
- bring in the literal add/drop info (times, etc.) to the sat solver to facilitate the solving process (CDCL, etc.)
