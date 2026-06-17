# MG-CAP Tournament

Issue: #1565

Primary endpoint: OOD episode success

## Run Budget

- Seeds: [0]
- Demo episodes: 2000
- Eval episodes per seed/split: 128
- Train steps per arm/seed: 8000
- Max episode steps: 100

## Validity Gate

- Status: fail
- Reasons: baseline OOD success below 0.15
- Best baseline: GRU_base
- Best baseline ID success: 1.000
- Best baseline OOD success: 0.000
- Random policy success: 0.000
- Oracle success: 1.000
- Overall verdict: invalid
- Priority-2 arms run: False

## Arms

| Arm | ID success | OOD DoorKey | OOD transfer | Params |
| --- | ---: | ---: | ---: | ---: |
| GRU_base | 1.000 [1.000, 1.000] | 0.000 [0.000, 0.000] | 0.000 [0.000, 0.000] | 81975 |
| Transformer_base | 1.000 [1.000, 1.000] | 0.008 [0.000, 0.023] | 0.000 [0.000, 0.000] | 78807 |

## Candidate Deltas

Priority-2 candidates were not run because the task-validity gate failed.

