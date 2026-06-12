# DGT L1 tiny-sequence controls

- Status: `pass`
- Review status: `pass`
- Evidence scope: `bounded-tiny-sequence`
- Step-ladder verdict: `scoped-review-signal`
- Step-ladder crossover: `no-information-starved-crossover-observed`
- L1 OOD mechanism verdict: `memorization`
- L1 OOD mechanism confidence: `medium`
- Seeds: `16`
- Compute units: `618.430464`
- Parameter count: `8388`
- Construct validity: `pass`

## Hardgates

- `L1-REVIEW-HG1`: `pass` - five L1 arms have true-training metrics while ledger, jet, and classifier metrics are owner-required boundaries
- `L1-REVIEW-HG2`: `pass` - seed-paired DGT minus information-starved baseline in-distribution accuracy CI95-low is positive
- `L1-REVIEW-HG3`: `pass` - seed-paired DGT minus matched-random accuracy CI95-low is positive with structural marginals preserved
- `L1-REVIEW-HG4`: `pass` - matched-random structural control preserves marginals and no L1 arm reports owner-required ledger, jet, or classifier metrics
- `L1-REVIEW-HG5`: `pass` - parameter-matched and compute-matched controls satisfy owner-local fairness ledgers
- `L1-REVIEW-HG6`: `pass` - independent replay, negative witnesses, and bounded order-two scope are fail-closed
- `L1-REVIEW-HG7`: `pass` - review verdict is emitted only after L1-REVIEW-HG1 through L1-REVIEW-HG6 pass

## L1 Step Ladder

- `36` steps: DGT acc `0.311768`, information-starved acc `0.065430`, matched-random acc `0.058105`, DGT-information-starved gap `0.246338`
- `72` steps: DGT acc `0.630859`, information-starved acc `0.065186`, matched-random acc `0.062500`, DGT-information-starved gap `0.565673`
- `144` steps: DGT acc `0.937500`, information-starved acc `0.068848`, matched-random acc `0.061035`, DGT-information-starved gap `0.868652`
- `288` steps: DGT acc `0.981445`, information-starved acc `0.068848`, matched-random acc `0.057129`, DGT-information-starved gap `0.912597`
- `576` steps: DGT acc `0.981934`, information-starved acc `0.068603`, matched-random acc `0.058838`, DGT-information-starved gap `0.913331`

## L1 Step Hardgates

- `L1STEP-HG1`: `pass` - canonical step grid has 400 step/arm/seed CPU training cells
- `L1STEP-HG2`: `pass` - every ladder cell is true CPU training with parameter updates and loss decrease
- `L1STEP-HG3`: `pass` - every ladder step has positive compute and parameter ledgers
- `L1STEP-HG4`: `pass` - crossover is mechanically derived from the 36-step DGT anchor and per-step accuracy means
- `L1STEP-HG5`: `pass` - matched-random structural arm must not reach the 36-step DGT anchor tolerance band

## L1 OOD Mechanism

- Verdict: `memorization`
- Diagnostic confidence: `medium`
- `train_seen_high_frequency_pair`: accuracy `0.991453`, margin `0.857049`, examples `234`
- `train_seen_low_frequency_pair`: accuracy `0.275944`, margin `-0.548865`, examples `3787`
- `train_unseen_pair`: accuracy `0.000000`, margin `-2.461352`, examples `76`
- `ood_dependency_shift_pair`: accuracy `0.069580`, margin `-2.056503`, examples `4096`

## L1 OOD Hardgates

- `L1OOD-HG1`: `pass` - all required pair-frequency and dependency-shift strata are present for every arm
- `L1OOD-HG2`: `pass` - read-only mechanism probe rows are canonical CPU forward passes
- `L1OOD-HG3`: `pass` - probe contains aggregate true-class logits and margins without parameter mutation
- `L1OOD-HG4`: `pass` - matched-random control rows are present and remain diagnostic controls rather than verdict owners
- `L1OOD-HG5`: `pass` - mechanism diagnosis uses the existing pointer-backed order-two task source
- `L1OOD-HG6`: `pass` - mechanism verdict is mechanically selected from the registered verdict set

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
