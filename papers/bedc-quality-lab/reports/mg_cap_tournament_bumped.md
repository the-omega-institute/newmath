# MG-CAP Tournament

Issue: #1565

Primary endpoint: OOD episode success

## Run Budget

- Seeds: [0]
- Demo episodes: 3000
- Eval episodes per seed/split: 128
- Train steps per arm/seed: 15000
- Max episode steps: 256

## Validity Gate

- Status: fail
- Reasons: baseline ID success below 0.80, baseline OOD success below 0.15
- Best baseline: GRU_base
- Best baseline ID success: 0.000
- Best baseline OOD success: 0.000
- Random policy success: 0.007
- Oracle success: 1.000
- Overall verdict: invalid
- Priority-2 arms run: False

## Arms

| Arm | ID success | OOD DoorKey | OOD transfer | Params |
| --- | ---: | ---: | ---: | ---: |
| GRU_base | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 81975 |
| Transformer_base | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 78807 |

## Candidate Deltas

Priority-2 candidates were not run because the task-validity gate failed.

