# INFO v1.0.0

**Certified Algorithmic Information Theory, Ring-0 Pure-GPR Hutter Context-Mixing & Law-Induction Codec, Causal MDL & Combinatorial Bounds**

`INFO v1.0.0` unifies algorithmic coding foundations, context-vs-induction separation, finite coding/channel bounds, causal identifiability, and Lean 4 kernel Proof-DAG MDL distillation on top of `../FLOW` (`v9.0.0`, `Flow.Schema` 256-slot `16,384B` ABI) across five formally verified Lean 4 pillars (`89` theorems total, `0 sorryAx`, `0 Lean.ofReduceBool`):

1. **Algorithmic Coding, E1/E2/E3 Invariants & Structural α-MDL (`Info.Coding` — `28` theorems)**:
   - Pigeonhole incompressibility no-go, Kraft–McMillan prefix-tree inequality, Solomonoff/Bayes mixture dominance, Krichevsky–Trofimov (KT) exact rational conservation recurrence, 32-bit `E1/E2/E3` binary arithmetic renormalization & `bv_decide` bit-recovery proofs, plus De Bruijn α-canonicalization idempotency/renaming invariance (`deBruijnCanon_idempotent`, `deBruijnCanon_map_inj`) and Joint MDL refactoring breakeven (`mdl_no_free_abstraction`, `mdl_refactor_breakeven`, `mdl_asymmetric_hierarchy`).
2. **Context Blindness No-Go, Law Induction & Regime Switching (`Info.Induction` — `18` theorems)**:
   - Depth-$k$ Markov/CTW statistical blindness no-go vs. online algebraic induction zero-residual `bv_decide` proofs (`LFSR-23`, `CA Rule-30` 32-bit periodic ring, and `Mod-65536` Affine 4-step Hensel inversion) plus non-stationary switching vs. static mixture dominance.
3. **Discrete DPI, Sphere Packing & Zero-FP Delsarte LP Duality (`Info.Bounds` — `17` theorems)**:
   - Exact $L_1$/Total-Variation Data Processing Inequality contractions, Singleton/Hamming perfect packing (`[7,4,3]`, `[23,12,7]`), and exact rational integer LP weak duality certifying Ring-0 Delsarte Krawtchouk dual vectors.
4. **Observational Equivalence, Balke–Pearl IV & Causal MDL (`Info.Causal` — `16` theorems)**:
   - Distinct interventional causal mechanisms with identical joint distributions, non-parametric Balke–Pearl 16-response-strata Instrumental Variable ACE bounds (`[4/32, 26/32]`), and asymmetric interleaved Causal MDL under invariant Markov mechanisms.
5. **Lean 4 Kernel Proof-DAG & Reflective Proof-Term MDL (`Info.ProofMDL` — `10` theorems)**:
   - Exponential tree-vs-DAG sharing (`exprDagSize_le_treeSize`), soundness-preserving dead-lemma pruning monotonicity (`dead_lemma_pruning_cost_le`, `dead_lemma_pruning_preserves_deps`), proof-factoring Joint ΔMDL breakeven (`proof_factoring_breakeven`, `proof_no_free_factoring`), reflective kernel-decision dominance over expanded proof trees (`reflective_certificate_dominance`), α-renaming invariance (`alpha_expr_constIds_rename_invariance`), and reverse-reach load-bearing blueprint core lower bounds (`proof_blueprint_core_lower_bound`).

## Empirical Validation ("Compression Is Intelligence")

Unlike toy evaluators, `INFO` is audited by an `8`-gate build pipeline (`make verify-all`) and `6` end-to-end empirical test suites (`make experiments`) with a **standalone zero-heap decompressor (`build/info_decomp`, `34,072 B`)** verifying **100% SHA-256 bit-exact roundtrip** across every compressed payload:

### 1. Compression Ladder & Hutter Self-Extracting Total Size (`64 KB` Benchmarks)
Measured on real C17/Python/Markdown corpora, analytical depth-2 FSMX Markov source ($H^* = 5.001\text{ bpb}$), and non-cycling algorithmic generators (period $> 64\text{ KB}$):

| Corpus (`65,536 B`) | `deflate -9` | `zstd -19` | `bzip2 -9` | `lzma -9` | `INFO` (`bpb`) | `INFO` Hutter Total (`payload + info_decomp`) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `docs_real` (Markdown & prose) | `3.122` | `3.010` | `2.907` | `2.954` | **`2.705`** | `56,232 B` |
| `code_real` (`INFO` C17 sources) | `1.792` | `1.659` | `1.622` | `1.549` | **`1.435`** | `45,830 B` |
| `py_stdlib` (`argparse`/`difflib`/`inspect`/`json`) | `1.802` | `1.680` | `1.582` | `1.676` | **`1.498`** | `46,342 B` |
| `fsmx_exact` ($H^* = 5.001\text{ bpb}$) | `5.777` | `5.421` | `5.955` | `5.559` | **`5.231`** | `76,924 B` |
| `alg_lfsr23` (`LFSR-23` non-cycling) | `8.003` | `8.002` | `8.075` | `8.008` | **`0.006`** | **`34,121 B`** (`49 B` + `34,072 B`) |
| `alg_ca32_rule30` (`CA32 Rule-30`) | `8.003` | `8.002` | `8.077` | `8.008` | **`0.019`** | **`34,227 B`** (`155 B` + `34,072 B`) |
| `alg_affine16` (`Affine Mod-65536`) | `8.003` | `8.002` | `7.408` | `8.008` | **`0.017`** | **`34,211 B`** (`139 B` + `34,072 B`) |

*(Note: on `alg_affine16`, `bzip2 -9` captures trivial mod-$2^k$ low-bit cycles $2,4,8,16$ at `7.408 bpb`, still exceeding `INFO` payload by $> 435\times$ and `INFO` Hutter Total by $> 26\text{ KB}$.)*

### 2. Downstream Intelligence, Switching Redundancy & Delsarte Atlas
- **Zero-Shot 5-Domain Temporal Holdout Classification (`experiments/intelligence_downstream.py`)**: `INFO` conditional compression achieves **`5/5` (`100.0%`)** across `C17`, `Lean4`, `English`, `LFSR23` (`0.0020 bpb`), and `CA32` (`0.0244 bpb`), where `deflate -9` gains `1.06%` on both algorithmic domains and misclassifies `CA32`.
- **Causal Direction & Spike Latency**: Interleaved `causal-mdl` recovers **`4/4` (`100.0%`)** non-invertible ICM causal directions (`X -> Y`) vs. permutation-blind symmetric `deflate`; online surprise tracker detects injected regime switch at **`+0 B` latency** (`0.00 b/B` clean peak vs. `19.05 b/B` spike).
- **CTW & Switching Redundancy (`experiments/ctw_switching_atlas.py`)**: Cross-checks Ring-0 KT conservation and multi-switch dominance across finite horizons `512..4096 B`.
- **Exact Rational Delsarte LP Atlas (`experiments/delsarte_coding_atlas.py`)**: Solves Delsarte's primal LP using pure-Python `fractions.Fraction` Simplex with Bland's rule across `n = 4..10, d = 3..5`, verifying strong duality and `SEARU <= floor(A_LP)` on every row (`EXACT` match on `[7,3]=16`, `[7,4]=8`).
- **Structural α-Canonicalization & Ecosystem MDL Auditor (`experiments/ecosystem_mdl_audit.py`, `tools/info_ecosystem_audit.py`)**: Verifies De Bruijn α-invariance across C17/Lean4/Python (`raw_NCD = 0.542 -> alpha_NCD = 0.017`) and audits `3,451` source files across `FLOW`, `ELE`, `CHEM`, `QUA`, `ECON`, `PHY`, `SOUND`, and `INFO`. `classify_file_role` & `classify_block_kind` separate actionable `logic` clusters from `abi_header` / `experiment_script` / `domain_oracle` / `data_manifest` / `data_table` / `schema_layout` noise; across Wave 1–2 refactoring on `FLOW v9.0.0`, remaining logic-only `ΔMDL` dropped from `7,427 B` baseline down to `1,733 B` across `7` actionable logic clusters (plus `4` filtered non-PR clusters).
- **Lean 4 Kernel Proof-DAG & Proof-Term MDL Distillation (`experiments/lean_proof_distill.py`, `tools/lean_expr_export.lean`, `tools/info_lean_distill.py`)**: Exports memoized `Lean.Environment` kernel `Expr` DAGs (`--lang expr` `INFO_LANG_LEAN_EXPR` canonicalizer keeping dotted constants and `BV<n>`/`REF<n>`/`LV<n>` de Bruijn indices), compresses `BloatedDemo` (`decls=7, dead=2, clones=4, ΔMDL=+897.1 B, DAG=4,602, α-MDL=2,988.9 B`) -> `DistilledDemo` (`decls=2, dead=0, leanchecker PASS, DAG=1,868, α-MDL=2,100.1 B`), and audits live `.olean` kernel modules across `Info.Theory` (`175.95x` DAG/tree sharing, `10` clones), `Flow.Math` (`53.95x`, `14` clones), `Sound.Theory` (`141.6x`, `2` clones), `Phy.Noether` (`42,702.44x`), `EleCert` (`81.42x`), `EconCert` (`58.81x`), and `ChemCert` (`147.52x`, `0` dead, `0` clones).

## Architecture

- [`Info/Coding.lean`](Info/Coding.lean), [`Info/Induction.lean`](Info/Induction.lean), [`Info/Bounds.lean`](Info/Bounds.lean), [`Info/Causal.lean`](Info/Causal.lean), [`Info/ProofMDL.lean`](Info/ProofMDL.lean), [`Info/Theory.lean`](Info/Theory.lean): Pure Lean 4 foundations (`28 + 18 + 17 + 16 + 10 = 89` theorems, `0 sorryAx`, `0 Lean.ofReduceBool`).
- [`Info.lean`](Info.lean): Pure `Flow.Schema` `256`-slot (`16,384 B`) ABI compiler emitting zero-`memcpy` `build/info_schema_abi.h` (`0` local theorems/lemmas/axioms).
- [`include/info.h`](include/info.h) & [`src/info_ring0.c`](src/info_ring0.c): Freestanding Ring-0 Pure-GPR C17 kernel (`0` undef symbols, `0` `udiv`/`sdiv`/FPU/SIMD/indirect calls, `C++20` header clean, `clang-tidy` `0` warnings). Implements 10-expert Hutter logistic mixer (`ord0`, `ord1`, tagged `ord2..ord6`/`sparse`/`word_tbl`, 1 MiB `match`, online GF(2) Berlekamp–Massey + mod-65536 4-step Hensel Affine + W=32 Rule-30 CA), SSE calibration, `"INF1"` framing, Ring-0 De Bruijn α-canonicalizer (`info_alpha_canonicalize`, including `INFO_LANG_LEAN_EXPR` for `expr`), Joint MDL evaluator (`info_eval_joint_mdl`), CTW/Delsarte/Balke–Pearl classifiers, and Causal MDL.
- [`src/info_decomp_main.c`](src/info_decomp_main.c): Zero-heap standalone `"INF1"` decompressor (`build/info_decomp`, `34,072 B`).
- [`src/info_cert.h`](src/info_cert.h) & [`src/info_cli.c`](src/info_cli.c): Zero-heap, zero-`leanshared` host CLI (`build/info`), `18`-suite `selftest` (`T1..T18`), and live `.lean` / `"FIR1"` certificate emitter.
- [`oracles/verify_info_oracle.py`](oracles/verify_info_oracle.py): Gate 5 independent exact-rational oracle (`6/6` `info_decomp` SHA-256 checks + all `4` classifiers + `5/5` live `lean -DwarningAsError=true` & `leanchecker` cert replays + α-MDL invariance checks across `c`/`lean`/`py`/`expr`).
- [`tools/info_sabotage_check.py`](tools/info_sabotage_check.py): Gate 6 parallel `42`-mutant single-fault C17 verification suite across `14` categories (`42/42 = 100.0%` killed), delegating to `../FLOW/sdk/tools/flow_sabotage_runner.py`.
- [`tools/info_ecosystem_audit.py`](tools/info_ecosystem_audit.py), [`tools/lean_expr_export.lean`](tools/lean_expr_export.lean), [`tools/info_lean_distill.py`](tools/info_lean_distill.py): Cross-repository structural MDL auditor and Lean 4 kernel Proof-DAG distiller.

## Build, 8-Gate Verification & CLI

```sh
make fmt && make clean && make -j verify-all && make experiments
```

Standalone CLI & verification examples:

```sh
./build/info selftest
./build/info compress   <in> <out.inf> [--no-alg]
./build/info decompress <in.inf> <out>
./build/info_decomp     <in.inf> <out>
./build/info eval-bpb   <in> [--no-alg] [--out-json build/eval.json]
./build/info ncd        <a> <b> [--out-json build/ncd.json]
./build/info alpha-canon <in> <out> [--lang raw|c|lean|py|expr]
./build/info alpha-ncd  <a> <b> [--lang raw|c|lean|py|expr] [--out-json build/ancd.json]
./build/info eval-mdl-group [--alpha] [--lang raw|c|lean|py|expr] [--shared <m>] [--out-json build/mdl_grp.json] <f1> ...
./build/info causal-mdl <x> <y> [--out-json build/mdl.json]
python3 tools/info_ecosystem_audit.py --roots ../FLOW ../ELE ../CHEM ../QUA ../ECON ../PHY ../SOUND .
python3 tools/info_lean_distill.py --module Info.Theory --lean-path build/lean

./build/info classify-ctw        --out-json build/certs/ctw.json
./build/info classify-separation --out-json build/certs/sep.json
./build/info classify-delsarte   --out-json build/certs/delsarte.json
./build/info classify-causal     --out-json build/certs/causal.json

./build/info hunt alg-blindspot --seed 0x5ACE1   --out-lean build/certs/InfoHuntAlg.lean      --out-fir build/certs/alg.fir      --out-json build/certs/alg.json
./build/info hunt ctw-switch    --seed 0x42      --out-lean build/certs/InfoHuntCtw.lean      --out-fir build/certs/ctw.fir      --out-json build/certs/ctw.json
./build/info hunt delsarte-gap                   --out-lean build/certs/InfoHuntDelsarte.lean --out-fir build/certs/delsarte.fir --out-json build/certs/delsarte.json
./build/info hunt balke-pearl                    --out-lean build/certs/InfoHuntBP.lean       --out-fir build/certs/bp.fir       --out-json build/certs/bp.json
./build/info hunt causal-mdl    --seed 0x77      --out-lean build/certs/InfoHuntCausal.lean   --out-fir build/certs/causal.fir   --out-json build/certs/causal.json
```
