build.log                     fresh build of CompAudit, CompFinal, CompLinear (exit 0). It also
                              contains the #check/#print output of CompAudit as info lines.
axioms_and_statements.log     `lake env lean CompAudit.lean`: full theorem types, definitions,
                              #print axioms (19 results, all [propext, Classical.choice, Quot.sound]).
lean4checker.log              `lake env lean4checker <M>` for the six new modules: exit status 0 each.
lean4checker_fresh.log        `lake env lean4checker --fresh CompAudit` (replays the whole
                              environment, Mathlib included). Started 22:34 UTC on 26 Sep 2026.
                              If this file is absent or has no exit status, the replay had not
                              finished when the folder was written; it will be added when it ends.
linearfinal_lean4checker_fresh_completed.log
                              The completed log of `lake env lean4checker --fresh LinearFinal`
                              from the linear_lean_2026-09-26 return, which was still running when
                              that return was written. It records exit status 0 (started 20:10:21,
                              finished 21:08:03 UTC). lean4checker prints nothing on success. The
                              earlier return itself was left unchanged.
