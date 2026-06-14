# DGT L1 tiny-sequence controls

- Status: `pass`
- Review status: `pass`
- Evidence scope: `bounded-tiny-sequence`
- Step-ladder verdict: `diagnostic-only`
- Step-ladder crossover: `no-diagnostic-crossover-observed`
- L1 OOD mechanism verdict: `brittle-rule`
- L1 OOD mechanism confidence: `medium`
- Fair L1 standing verdict: `bounded-negative`
- Fair L1 canonical axis action: `hold-current`
- Seeds: `16`
- Compute units: `931.332096`
- Parameter count: `12632`
- Construct validity ledger: `pass`

## Hardgates

- `L1-REVIEW-HG1`: `pass` - four L1 arms have true-training metrics while ledger, jet, and classifier metrics are owner-required boundaries
- `L1-REVIEW-HG2`: `pass` - masked-tail input ablation is present as a diagnostic arm with seed-paired rows
- `L1-REVIEW-HG3`: `pass` - parameter- and compute-matched attention controls are present for fair comparison
- `L1-REVIEW-HG4`: `pass` - parameter-matched attention control uses self-attention and no L1 arm reports owner-required ledger, jet, or classifier metrics
- `L1-REVIEW-HG5`: `pass` - parameter-matched and compute-matched controls satisfy owner-local fairness ledgers
- `L1-REVIEW-HG6`: `pass` - independent replay, negative witnesses, and bounded order-two scope are fail-closed
- `L1-REVIEW-HG7`: `pass` - review verdict is emitted only after L1-REVIEW-HG1 through L1-REVIEW-HG6 pass

## L1 Step Ladder

- `36` steps: DGT acc `0.038086`, input-ablation acc `0.010986`, parameter-matched attention acc `0.009765`, DGT-input-ablation gap `0.027100`
- `72` steps: DGT acc `0.033936`, input-ablation acc `0.009277`, parameter-matched attention acc `0.012695`, DGT-input-ablation gap `0.024659`
- `144` steps: DGT acc `0.031494`, input-ablation acc `0.010986`, parameter-matched attention acc `0.009521`, DGT-input-ablation gap `0.020508`
- `288` steps: DGT acc `0.028564`, input-ablation acc `0.013428`, parameter-matched attention acc `0.010742`, DGT-input-ablation gap `0.015136`
- `576` steps: DGT acc `0.034180`, input-ablation acc `0.013672`, parameter-matched attention acc `0.010742`, DGT-input-ablation gap `0.020508`

## L1 Step Hardgates

- `L1STEP-HG1`: `pass` - canonical step grid has 320 step/arm/seed CPU training cells
- `L1STEP-HG2`: `pass` - every ladder cell is true CPU training with parameter updates and loss decrease
- `L1STEP-HG3`: `pass` - every ladder step has positive compute and parameter ledgers
- `L1STEP-HG4`: `pass` - crossover is mechanically derived from the 36-step DGT anchor and per-step accuracy means
- `L1STEP-HG5`: `pass` - parameter-matched attention crossover is recorded as diagnostic evidence only

## L1 OOD Mechanism

- Verdict: `brittle-rule`
- Diagnostic confidence: `medium`
- `train_seen_high_frequency_pair`: accuracy `0.250000`, margin `-0.576990`, examples `16`
- `train_seen_low_frequency_pair`: accuracy `0.312500`, margin `-0.996655`, examples `16`
- `train_unseen_pair`: accuracy `0.038086`, margin `-1.867281`, examples `4096`
- `heldout_pair`: accuracy `0.036865`, margin `-1.865080`, examples `4096`

## L1 OOD Hardgates

- `L1OOD-HG1`: `pass` - all required pair-frequency and held-out pair strata are present for every arm
- `L1OOD-HG2`: `pass` - read-only mechanism probe rows are canonical CPU forward passes
- `L1OOD-HG3`: `pass` - probe contains aggregate true-class logits and margins without parameter mutation
- `L1OOD-HG4`: `pass` - parameter-matched attention control rows are present and remain diagnostic controls rather than verdict owners
- `L1OOD-HG5`: `pass` - mechanism diagnosis uses the existing pointer-backed order-two task source
- `L1OOD-HG6`: `pass` - mechanism verdict is mechanically selected from the registered verdict set

## Fair L1 Construction

- OOD survivor present: `False`
- Construct validity: `construct-valid`
- `base`: in-dist acc `0.192627`, OOD acc `0.000977`, loss decrease `0.377059`
- `dgt`: in-dist acc `0.203613`, OOD acc `0.000000`, loss decrease `0.405523`
- `matched-random`: in-dist acc `0.160400`, OOD acc `0.000000`, loss decrease `0.305516`
- `parameter-matched`: in-dist acc `0.191406`, OOD acc `0.003906`, loss decrease `0.379724`
- `compute-matched`: in-dist acc `0.195068`, OOD acc `0.000977`, loss decrease `0.396454`

## Fair L1 Hardgates

- `FAIR-L1-HG1`: `pass` - every fair arm sees x_minus_1 and x_minus_2 and no forbidden feature name
- `FAIR-L1-HG2`: `pass` - train and OOD support partitions are disjoint and share the same label rule reference
- `FAIR-L1-HG3`: `pass` - fair L1 grid contains true CPU training rows with parameter movement and loss decrease
- `FAIR-L1-HG4`: `pass` - OOD gate records raw metrics and rejects lookup-only behavior
- `FAIR-L1-HG5`: `pass` - OOD survivor signals are routed to maintainer review rather than standing promotion
- `FAIR-L1-HG6`: `pass` - forbidden public-claim phrase audit is clean
- `FAIR-L1-HG7`: `pass` - construct-validity evaluation is folded into the DGT L1 controls payload

## Claim Capsule

- Scope: `bounded-tiny-sequence`
- Allowed claim: DGT L1 controls are ready for independent review on bounded tiny-sequence order-k training.

## Not Claimed

- Bounded tiny-sequence order-k training only.
- No production deployment claim.
- No global superiority claim.
- No LLM replacement claim.
- No universal training recipe claim.
- No full BEDC closure claim.
- No L2 or higher scaling claim.
- No natural-language capability claim.
- No component-causal stability beyond the #1168 measured owner.
