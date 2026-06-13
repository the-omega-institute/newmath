# Fair L1 Decision

- Status: `bounded-negative`
- Ladder state: `l1-bounded-negative`
- Failed gate: `FAIR-L1-HG2`

## Hardgates

- `FAIR-L1-HG1`: `pass` - required owner pointers resolve before any L1 decision is emitted
- `FAIR-L1-HG2`: `fail` - equal-step, equal-compute, equal-loss-decrease, and equal-validation-loss rows are resolved
- `FAIR-L1-HG3`: `fail` - baseline arm has enough task information for a fair architecture comparison
- `FAIR-L1-HG4`: `pass` - bounded L1 controls pass their owner-local review
- `FAIR-L1-HG5`: `fail` - step-ladder verdict supplies positive fair scaling evidence
- `FAIR-L1-HG6`: `fail` - OOD mechanism evidence is above boundary-only status
- `FAIR-L1-HG7`: `fail` - baseline can in principle express the target dependency

## Fair Alignment

- `equal-step`: `resolved` - `noninformative-dgt-separated`
- `equal-compute`: `resolved` - `noninformative-dgt-separated`
- `equal-loss-decrease`: `resolved` - `noninformative-dgt-separated`
- `equal-validation-loss`: `missing` - `validation-loss-owner-cell-missing`

## Boundary Ledger

- `FAIR-L1-HG2`: `bounded-negative` - one or more fair alignment rows are missing
- `FAIR-L1-HG3`: `bounded-negative` - baseline arm is information-starved or input-accessibility rows mark missing variables
- `FAIR-L1-HG5`: `bounded-negative` - step-ladder evidence does not support fair scaling promotion
- `FAIR-L1-HG6`: `bounded-negative` - OOD mechanism remains diagnostic or not claimed
- `FAIR-L1-HG7`: `bounded-negative` - baseline Bayes limit is chance under the owner construct-validity proof

## Not Claimed

- Bounded L1 tiny-sequence decision only.
- No L2 or higher scaling claim.
- No production deployment claim.
- No global model superiority claim.
- No LLM replacement claim.
- No OOD generalization claim.
- No architecture advantage claim.
