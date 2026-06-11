# DGT L1 tiny-sequence controls

- Status: `pass`
- Review status: `pass`
- Evidence scope: `bounded-tiny-sequence`
- Step-ladder verdict: `separation-persists`
- Step-ladder crossover: `no-base-crossover-observed`
- Seeds: `16`
- Compute units: `618.430464`
- Parameter count: `8388`

## Hardgates

- `L1-REVIEW-HG1`: `pass` - five L1 arms have true-training metrics while ledger, jet, and classifier metrics are owner-required boundaries
- `L1-REVIEW-HG2`: `pass` - seed-paired DGT minus base in-distribution accuracy CI95-low is positive
- `L1-REVIEW-HG3`: `pass` - seed-paired DGT minus matched-random accuracy CI95-low is positive with structural marginals preserved
- `L1-REVIEW-HG4`: `pass` - matched-random structural control preserves marginals and no L1 arm reports owner-required ledger, jet, or classifier metrics
- `L1-REVIEW-HG5`: `pass` - parameter-matched and compute-matched controls satisfy owner-local fairness ledgers
- `L1-REVIEW-HG6`: `pass` - independent replay, negative witnesses, and bounded order-two scope are fail-closed
- `L1-REVIEW-HG7`: `pass` - review verdict is emitted only after L1-REVIEW-HG1 through L1-REVIEW-HG6 pass

## L1 Step Ladder

- `36` steps: DGT acc `0.311768`, base acc `0.065430`, matched-random acc `0.058105`, DGT-base gap `0.246338`
- `72` steps: DGT acc `0.630859`, base acc `0.065186`, matched-random acc `0.062500`, DGT-base gap `0.565673`
- `144` steps: DGT acc `0.937500`, base acc `0.068848`, matched-random acc `0.061035`, DGT-base gap `0.868652`
- `288` steps: DGT acc `0.981445`, base acc `0.068848`, matched-random acc `0.057129`, DGT-base gap `0.912597`
- `576` steps: DGT acc `0.981934`, base acc `0.068603`, matched-random acc `0.058838`, DGT-base gap `0.913331`

## L1 Step Hardgates

- `L1STEP-HG1`: `pass` - canonical step grid has 400 step/arm/seed CPU training cells
- `L1STEP-HG2`: `pass` - every ladder cell is true CPU training with parameter updates and loss decrease
- `L1STEP-HG3`: `pass` - every ladder step has positive compute and parameter ledgers
- `L1STEP-HG4`: `pass` - crossover is mechanically derived from the 36-step DGT anchor and per-step accuracy means
- `L1STEP-HG5`: `pass` - matched-random structural arm must not reach the 36-step DGT anchor tolerance band

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
