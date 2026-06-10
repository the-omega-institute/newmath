# DGT L1 tiny-sequence controls

- Status: `ready`
- Review status: `ready`
- Evidence scope: `bounded-tiny-sequence`
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
