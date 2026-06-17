# MG-CAP Tournament

Issue: #1565

Primary endpoint: OOD episode success

## Run Budget

- Seeds: [0, 1]
- Demo episodes: 400
- Eval episodes per seed/split: 64
- Train steps per arm/seed: 1000
- Max episode steps: 128

## Validity Gate

- Status: fail
- Reasons: baseline ID success below 0.80, baseline OOD success below 0.15
- Best baseline: Transformer_base
- Best baseline ID success: 0.016
- Best baseline OOD success: 0.000
- Random policy success: 0.000
- Oracle success: 1.000
- Overall verdict: invalid
- Priority-2 arms run: False

## Arms

| Arm | ID success | OOD DoorKey | OOD transfer | Params |
| --- | ---: | ---: | ---: | ---: |
| GRU_base | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 34135 |
| Transformer_base | 0.016 [0.000, 0.039] | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 32663 |

## Candidate Deltas

Priority-2 candidates were not run because the task-validity gate failed.

