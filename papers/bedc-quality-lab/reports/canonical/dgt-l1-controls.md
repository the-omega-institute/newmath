# DGT L1 tiny-sequence controls

- Status: `ready`
- Review status: `ready`
- Evidence scope: `bounded-tiny-sequence`
- Step-ladder verdict: `separation-persists`
- Step-ladder crossover: `no-base-crossover-observed`
- Seeds: `8`
- Compute units: `183.877632`
- Parameter count: `4988`

## Hardgates

- `L1-HG1`: `pass` - base transformer true-training control is parameter/compute matched
- `L1-HG2`: `pass` - matched-random structural true-training control preserves marginals and fails positive claim
- `L1-HG3`: `pass` - compute ledger has positive compute units for every arm/seed/step cell
- `L1-HG4`: `pass` - parameter ledger has positive parameter counts for every trained model arm
- `L1-HG5`: `pass` - negative witness sweep has real hit logic and resolving regression pointers
- `L1-HG6`: `pass` - independent replay records task digest, seed digest, and metric tolerance rows
- `L1-HG7`: `pass` - ClaimCapsule scope is bounded-tiny-sequence and all evidence pointers are owner pointers
- `L1-HG8`: `pass` - initial L1 output is ready for independent review but not review pass

## L1 Step Ladder

- `36` steps: DGT acc `0.288086`, base acc `0.062500`, matched-random acc `0.058105`, DGT-base gap `0.225586`
- `72` steps: DGT acc `0.604004`, base acc `0.069824`, matched-random acc `0.059570`, DGT-base gap `0.534180`
- `144` steps: DGT acc `0.942383`, base acc `0.070312`, matched-random acc `0.057617`, DGT-base gap `0.872071`
- `288` steps: DGT acc `0.981934`, base acc `0.068359`, matched-random acc `0.058594`, DGT-base gap `0.913575`
- `576` steps: DGT acc `0.982422`, base acc `0.068359`, matched-random acc `0.061523`, DGT-base gap `0.914063`

## L1 Step Hardgates

- `L1STEP-HG1`: `pass` - canonical step grid has 120 step/arm/seed CPU training cells
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
