# Alloy 6.2.0 Migration Plan (clafer and claferIG)

**Status**: Living document
**Version**: 0.2.0
**Date**: 2026-09-12
**Project**: HOARDE (Sigil-Logic Clafer fork, epic [HOARDE#608](https://github.com/Sigil-Logic/HOARDE/issues/608))
**Issue**: [#5](https://github.com/Sigil-Logic/clafer/issues/5)

---

## Purpose

This document is the audit and migration design for moving the Clafer toolchain's Alloy backend from Alloy 4.2 (2012) to the current stable Alloy release, **6.2.0** (2025-01-09), acquired from Maven Central (`org.alloytools:org.alloytools.alloy.dist:6.2.0`).  It records the empirical audit evidence (SL-DOM-P04), the exact API porting surface, the scope decisions the evidence forces, and the V&V plan.  It governs the paired changes in [Sigil-Logic/clafer](https://github.com/Sigil-Logic/clafer) and [Sigil-Logic/claferIG](https://github.com/Sigil-Logic/claferIG).

## Audit Environment

| Item | Value |
|---|---|
| Host | aarch64 macOS (Darwin 25.6.0), OpenJDK 21.0.2 (aarch64) |
| Baseline compiler | clafer 0.5.1, master @ `e430cf7` (fresh `stack build`, GHC 9.4.8) |
| Alloy 6.2.0 | `org.alloytools.alloy.dist-6.2.0.jar` from Maven Central, SHA-256 `6037cbeee0e8423c1c468447ed10f5fcf2f2743a2ffc39cb1c81f2905c0fdb9d` |
| Alloy 4.2 reference | `alloy4.2.jar` as committed on clafer master |
| Corpus | `test/positive/*.cfr` excluding `*.des.cfr` — 162 models |

## Empirical Audit Results

### Corpus acceptance sweep (clafer-generated `.als` under Alloy 6.2.0)

Every corpus model was compiled with the baseline compiler (`clafer -s -k -m alloy --self-contained`) and each generated `.als` was parsed and type-checked by Alloy 6.2.0 (`java -jar <dist>.jar commands <file>`, exit-code gated).

| Class | Count | Result under 6.2.0 |
|---|---|---|
| Not Alloy-compilable (pre-existing: reals / product operator) | 5 | No `.als` produced under 4.2 baseline either; unchanged |
| Static Alloy models | 115 | **114 PASS**, 1 FAIL (`gi84-parent-top-level-abstract`) |
| Behavioral models (AlloyLtl generator, `tmp_*` family) | 42 | **42 FAIL** |

Key findings:

1. **The static Alloy generator output is already Alloy 6.2-compatible.**  No generator changes are required for the static subset; generated text is unchanged, so the `.als` regression baselines (`test/regression/*.als.reg`) and the 47-model PLE corpus byte-identity are preserved by construction.
2. **The single static failure is pre-existing, not a 6.2 regression.**  `gi84-parent-top-level-abstract.als` references a field `@r_c0_Feature` that does not exist in the generated model; Alloy **4.2 rejects it with the identical error** ("The name \"@r_c0_Feature\" cannot be found").  It has gone unnoticed because `runValidate` invokes the validator via `void $ system` — validation is non-gating.  Disposition: file a follow-on generator-bug issue; out of scope here.
3. **All 42 behavioral failures originate in the LTL encoding, and the port is not mechanical.**  Alloy 6 made `'` the temporal prime operator, so primed identifiers (`s'` in `Generator/stateTrace.als`; `t'`, `t''`, … freshened per nesting level by `Generator/AlloyLtl.hs`) are now syntax errors.  Renaming the primes in five sampled models lets two parse, but the deeper models still fail — arbitrarily deep primes (`t'''`, `t''''`) and, after full renaming, **type errors** in the trace encoding (e.g., `tmp_Global05.als:74`), i.e., 4.2→6 resolver/type-system differences reach the encoding's semantics.  Since Alloy 6's native temporal logic (Electrum: `var` sigs, LTL operators) supersedes the hand-rolled `stateTrace.als` trace encoding entirely, porting the old encoding would be effort spent on an artifact the follow-on issue replaces.

### Solver stack on aarch64 (the claferIG unblock)

Alloy 6.2.0 bundles per-platform solver natives inside the dist jar (self-extracted at run time by the Kodkod native loader — no `java.library.path` staging, no separate `lib/` directory):

| Platform | Bundled natives |
|---|---|
| `darwin/arm64` | `libminisat.dylib`, **`libminisatprover.dylib`**, `libglucose.dylib`, `plingeling`, `electrod` |
| `darwin/amd64`, `linux/amd64`, `windows/amd64` | same set (`.so`/`.dll` respectively) |

Verified on this aarch64 macOS host with the 6.2.0 CLI: `solvers` reports platform `darwin/arm64`; `exec -s minisat.prover` returns **SAT** on a Clafer-generated model and **UNSAT** on a deliberately unsatisfiable model — i.e., the MiniSat **prover** (the UNSAT-core solver claferIG requires) runs natively on Apple Silicon.  This resolves the field-note blocker on [#5](https://github.com/Sigil-Logic/clafer/issues/5): after this port, claferIG becomes locally buildable and testable on aarch64 hosts for the first time.  Raw probe transcripts are preserved in claferIG `.evidence/alloy62-arm64-probe/`.

### API porting surface (claferIG shim), pinned against 6.2.0

Alloy 5 repackaged the API; 6.x is source-incompatible with the 4.2 shim.  The complete surface touched by `AlloyIG.java`, `Util.java`, and `AlloyCompiler.java`, with the pinned 6.2.0 replacement:

| Alloy 4.2 | Alloy 6.2.0 | Notes |
|---|---|---|
| `edu.mit.csail.sdg.alloy4compiler.ast.*` | `edu.mit.csail.sdg.ast.*` | `Command`, `CommandScope`, `Sig`, `Expr`, `ExprList`, `ExprUnary`, `ExprLet` |
| `edu.mit.csail.sdg.alloy4compiler.parser.*` | `edu.mit.csail.sdg.parser.*` | `CompModule`, `CompUtil` |
| `edu.mit.csail.sdg.alloy4compiler.translator.*` | `edu.mit.csail.sdg.translator.*` | `A4Options`, `A4Solution`, `TranslateAlloyToKodkod` |
| `edu.mit.csail.sdg.alloy4.*` | unchanged | `A4Reporter`, `Err`, `ErrorSyntax`, `ErrorWarning`, `Pos`, `SafeList` |
| custom `AlloyCompiler.parse(rep, model)` (internal-parser override for in-memory models) | `CompUtil.parseEverything_fromString(rep, model)` | **The override class is deleted** — the modern API parses from a string directly |
| `new Command(pos, label, check, overall, bitwidth, maxseq, expects, scope, addl, formula, parent)` (11-arg) | 15-arg ctor `Command(Pos, Expr nameExpr, String, boolean, int overall, int bitwidth, int maxseq, int minprefix, int maxprefix, int expects, Iterable<CommandScope>, Iterable<Sig>, ExprVar commandKeyword, Expr formula, Command parent)`; scope changes via `command.change(Sig, boolean, int)` / `change(ConstList<CommandScope>)` | `setScopeSize`/`setCommandScopeSize` hand-rolling collapses into `change(...)`; overall/bitwidth rewrites use the full ctor preserving `minprefix`/`maxprefix`/`maxstring`/`nameExpr`/`commandKeyword` |
| `new CommandScope(pos, sig, isExact, start, end, incr)` (6-arg) | `CommandScope(Pos, Pos sigPos, Sig, boolean, int, int, int)` (7-arg) | 3-arg convenience ctor unchanged |
| `options.solver = A4Options.SatSolver.MiniSatProverJNI` | `options.solver = SATFactory.get("minisat.prover")` (`kodkod.engine.satlab.SATFactory`; `SATFactory.find(id)` for availability probe, `SATFactory.DEFAULT` = SAT4J fallback) | `A4Options.solver` changed type to `SATFactory` |
| `System.loadLibrary("minisatprover"/"minisatproverx1")` at startup | **deleted** | 6.2 self-extracts natives from the dist jar; availability handled via `SATFactory.find` with explicit fallback + stderr notice |
| `TranslateAlloyToKodkod.execute_command(rep, sigs, cmd, opts)` | unchanged signature | |
| `A4Reporter.minimized(Object, int, int)`, `warning(ErrorWarning)` | unchanged | UNSAT-core detection idiom preserved |
| `ans.writeXML(PrintWriter, macros, sources)`, `ans.next()`, `ans.satisfiable()`, `ans.highLevelCore()` | signatures unchanged; a **null macros iterable now NPEs** (see Port Findings) — pass an empty list | |
| `Sig.isOne/isLone/isSome` (public final `Pos`), `sig.getFacts()` | unchanged (plus new `isVariable`) | The reflective save/restore-state machinery in `Util.java` ports as-is |
| `ExprList.make(pos, closingBracket, op, List)`, `ExprLet.make(pos, var, expr, sub)`, `ExprUnary.op.make(pos, sub)` | unchanged | `removeSubnode` constraint-removal ports as-is |
| `Pos(String, int, int, int, int)` | unchanged | |

Residual risk: the shim still reaches into non-stable internals (reflective writes to `Sig` fields, `CompModule` internals via `parseEverything_fromString` semantics), so the Alloy version stays **pinned at exactly 6.2.0** and this table documents the touched surface, per the issue's risk note.

## Migration Design

### clafer (compiler) changes

1. **Jar acquisition** (`Makefile`): replace the `alloytools.org` download of `alloy4.2.jar` with a pinned Maven Central fetch of `org.alloytools.alloy.dist-6.2.0.jar`, verified against the SHA-256 above (supply-chain hygiene); `git rm alloy4.2.jar` (no bundled jars); gitignore the downloaded artifact; update the `install` target to stage the new jar.
2. **Validator** (`src/Language/Clafer.hs`): `validateAlloy` becomes `java -jar <tooldir>/org.alloytools.alloy.dist-6.2.0.jar commands <file>` (parse + type-check; exits nonzero on rejection).  The 4.2 entry class `ExampleUsingTheCompiler` no longer exists.  Validation stays non-gating (`void $ system`) exactly as today; gating is a candidate follow-on once gi84 is fixed.
3. **Help/docs** (`src/Language/Clafer/ClaferArgs.hs`, `README.md`): "Alloy 4.2" → "Alloy 6.2"; `--tooldir` text updated to the new jar name.
4. **Test harness** (`test/Makefile`): the `../alloy4.2.jar` existence check and any staging references follow the new jar name.
5. **Generator**: **no changes to `Generator/Alloy.hs`** (static output is 6.2-clean, keeping regression baselines and PLE byte-identity intact).  `Generator/stateTrace.als` and `Generator/AlloyLtl.hs` are **not ported** (see Scope decisions).

### claferIG changes

1. **Shim port** (`src/org/clafer/ig/AlloyIG.java`, `Util.java`): apply the API table above; delete the startup `loadLibrary` block; solver selection = `SATFactory.find("minisat.prover")` with documented SAT4J fallback (stderr notice, since UNSAT-core features degrade without the prover).
2. **Delete** `src/edu/mit/csail/sdg/alloy4compiler/parser/AlloyCompiler.java` (superseded by `CompUtil.parseEverything_fromString`).
3. **Manifest** (`src/manifest`): `Class-Path: org.alloytools.alloy.dist-6.2.0.jar`.
4. **Build** (`Makefile`): Maven Central fetch (pinned + checksum) replacing the `alloytools.org` download; **remove the `lib` target and all `lib/` staging** (natives now live inside the dist jar); `javac -release 17` so the committed `alloyIG.jar` stays runnable on the CI Temurin 17 toolchain regardless of the developer's local JDK; update `build`/`test`/`install` staging to the new jar name.
5. **Launcher** (`src/Language/Clafer/IG/AlloyIGInterface.hs`): drop `-Djava.library.path=<exec>lib` from the JVM invocation.
6. **Repo hygiene**: `git rm alloy4.2.jar lib/libminisatprover.dylib lib/libminisatprover.so lib/minisatprover.dll`; update `claferIG.cabal` extra files accordingly; gitignore the downloaded dist jar; rebuild and commit `alloyIG.jar` against 6.2.0.
7. **CI** (`.github/workflows/ci.yml`): drop the "Extract the MiniSat prover native" step; keep the x86_64 build/test/baseline-capture job; the baseline-capture step now captures 6.2 behavior for the comparison below.  Proposed addition: a `macos-latest` (arm64) build/test job as durable CI evidence of the Apple Silicon unblock.
8. **Docs** (`README.md`): Alloy 6.2.0 prerequisites, Maven Central acquisition, removal of the native-library installation steps, and an Apple Silicon support note.

## Scope Decisions (resolved at Checkpoint 1)

All four decisions below were reviewed and resolved by Frank Zeyda at Checkpoint 1 ([PR #10 comment](https://github.com/Sigil-Logic/clafer/pull/10#issuecomment-5647934606)); decisions 3 and 4 changed from the original proposal, as recorded here.

1. **AlloyLtl / `stateTrace.als` deferral.**  The behavioral (LTL) generator path remains 4.2-targeted and is deferred to the already-anticipated temporal follow-on issue ("exploiting Alloy 6 temporal logic for behavioral Clafer"), to be filed as part of this PR with the audit evidence above.  Rationale: the primed-identifier fix alone is insufficient (deep primes plus type errors in the trace encoding under 6.2), the encoding is superseded by Alloy 6's native temporal operators, no static-corpus or claferIG behavior depends on it (claferIG rejects behavioral `tmp.als` input today), and the issue's own out-of-scope note anticipates exactly this split.  **Consequence**: the first acceptance criterion is read as the full *static* Alloy corpus (115 models; 42 behavioral models documented as deferred), with the pre-existing gi84 failure documented and issue-tracked.
2. **gi84 latent generator bug** is documented and filed as a follow-on (invalid field reference for top-level abstract clafers; rejected identically by 4.2 and 6.2; masked by non-gating validation).
3. **`alloyIG.jar` is no longer a committed artifact** (resolved: Option B).  It is built from source by `make` (`javac --release 17` against the pinned Alloy jar) and gitignored: single source of truth, no stale-jar hazard, no binary review surface, and the better supply-chain story.  Consumers of the old binary-distribution flow build it with `make alloyIG.jar`.
4. **Alloy version is pinned at 6.2.0** everywhere (Makefiles, manifest, validator, docs) because the shim touches non-stable internals.
5. **claferIG CI gains a `macos-latest` (arm64) build/test job** (resolved: include) as durable evidence of the Apple Silicon unblock, alongside the x86_64 Linux job that also captures the behavioral baseline.

## V&V Plan

| Evidence | Method | Gate |
|---|---|---|
| clafer test suite | `stack test` locally and on x86_64 CI | green |
| claferIG test suite | `make test` (full suite incl. `strMapCheck`) on x86_64 CI **and locally on aarch64** (first time possible) | green |
| Corpus acceptance (AC 1) | 6.2.0 `commands` sweep over all static-corpus `.als` (as in the audit), re-run on the ported branch | 114/115, gi84 documented |
| PLE regression (AC 5) | 47-model corpus (HOARDE 22, NINJA 14, cryptol-agent 11), ported binary vs. frozen master baseline binary, `diff -r` over `.als`/`.cfr-map`/`.cfr-scope` + exit/stdout/stderr | byte-identical |
| PLE analysis (AC 5) | each corpus `.als` analyzed by Alloy 6.2.0 (`exec`, SAT expected) | documented per model |
| Behavioral baseline (AC 4) | re-run `scripts/capture-alloy42-baseline.sh` on the ported branch (x86_64 CI, same scope/corpus) and compare against frozen `master:.evidence/alloy42-baseline/` (16 models, 1801 instances): per-model exit codes, instance counts, instance-set equality modulo enumeration order, enumeration-order drift, XML/JSON format drift | differences documented with rationale; re-baseline commit |
| Apple Silicon unblock | local aarch64 claferIG build + test run + instance generation; probe transcripts in `.evidence/alloy62-arm64-probe/`; proposed `macos-latest` CI job | evidence captured either way |

## Port Findings (implementation phase)

Three empirical findings from the shim port, folded into the design above:

1. **`A4Solution.writeXML` no longer tolerates a null macros iterable** (NPE in `A4SolutionWriter.writeInstance`, `extraSkolems`); the shim passes an empty list.  The 4.2 call passed `null`.
2. **Kodkod logs INFO progress to stderr** through the slf4j-simple binding bundled in the dist jar; the shim sets `org.slf4j.simpleLogger.defaultLogLevel=warn` (and the older property spelling) in `main` before any Alloy class loads, keeping claferIG's stderr clean.
3. **Solve time on a heavyweight corpus model is not a regression**: `ACCDemo_attributedFeatureModels.als` (integer `sum` at scope 10) solves in ~70 s under 6.2 on the audit host — and ~73 s under Alloy 4.2 with SAT4J on the same host.  6.2 is marginally faster; the cost is inherent to the model, and prover-vs-SAT4J makes no material difference (isolated by A/B runs of the ported shim).

## Risks

| Risk | Mitigation |
|---|---|
| Instance enumeration order differs under 6.2 solver stack | Expected; the baseline comparison isolates order-only drift from instance-set changes; re-baseline with rationale (AC 4) |
| 6.2 integer/overflow defaults differ from 4.2 in ways the encoding is sensitive to | `noOverflow` defaults to false (4.2-equivalent); bitwidth handling preserved via the ported `setBitwidth` op; baseline comparison surfaces any residual semantic drift |
| Internal-API drift on future Alloy upgrades | Exact-version pin + the API-surface table above document the exposure |
| `alloyIG.jar` built with a newer JDK unloadable on the CI/runtime JDK | jar built from source with `javac --release 17` (matches Alloy 6.2.0's own class-file level) |

---

*HOARDE Claude (working with Frank Zeyda)*

<!--
Local Variables:
auto-fill-mode: nil
End:
-->
