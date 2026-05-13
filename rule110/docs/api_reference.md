# Rule 110 API Reference

后续 worker 先从这里找 accessor。签名以公开头文件为准；示例只展示调用形态。

## `evaluator/rule110.h`

Paper anchor: Cook 2004 Rule 110 construction; Cook 2009 Rule 110 initial-state compiler.

### `r110_step`

```c
void r110_step(uint8_t *cells, size_t len);
```

原地执行一步 Rule 110。`cells` 是 0/1 array, `len` 是 cell 数量, 边界外 cell 按 0 处理。返回 `void`。

```c
uint8_t row[] = {0, 1, 1, 1, 0};
r110_step(row, 5);
```

### `r110_run_n_steps`

```c
void r110_run_n_steps(uint8_t *cells, size_t len, size_t n);
```

原地执行 `n` 步。返回 `void`。

```c
r110_run_n_steps(row, 5, 100);
```

### `r110_dump_state`

```c
void r110_dump_state(const uint8_t *cells, size_t len, FILE *out);
```

把 row 写成 `0` / `1` 字符串并追加换行。返回 `void`。

```c
r110_dump_state(row, 5, stdout);
```

## `evaluator/cyclic_tag.h`

Paper anchor: Cook 2009 §1.3 cyclic tag encoding; Neary-Woods 2007 efficient Rule 110 simulation.

公开头文件没有 `ct_step`; 单步调试用 `ct_run_until_halt(&state, 1)`。

### `CtState`

```c
typedef struct {
    uint8_t **productions;
    size_t *prod_lens;
    size_t num_productions;
    uint8_t *tape;
    size_t tape_len;
    size_t tape_cap;
    size_t pc;
    size_t steps_taken;
} CtState;
```

`productions` / `prod_lens` 是 appendants, `tape` 是当前 tape, `pc` 是 cyclic production index。

### `ct_init`, `ct_run_until_halt`, `ct_free`

```c
int ct_init(CtState *s, uint8_t **productions, size_t *prod_lens,
            size_t num_productions, const uint8_t *initial_tape,
            size_t initial_tape_len, size_t reserved_cap);
CtHaltReason ct_run_until_halt(CtState *s, size_t max_steps);
void ct_free(CtState *s);
```

`ct_init` 成功返回 `0`, 分配失败返回 `-1`。`ct_run_until_halt` 返回 `CT_HALT_EMPTY`, `CT_HALT_STEPLIMIT`, 或 `CT_HALT_OOM`。

```c
uint8_t p0[] = {1, 0};
uint8_t *prods[] = {p0};
size_t lens[] = {2};
uint8_t tape[] = {1};
CtState s;
if (ct_init(&s, prods, lens, 1, tape, 1, 64) == 0) {
    CtHaltReason h = ct_run_until_halt(&s, 1);
    ct_free(&s);
}
```

## `encoder/glider_phases.h`

Paper anchor: Martinez 2007 Table 2 / Appendix A; Martinez 2012 §3.1 phase notation.

### `glider_phase`

```c
const char *glider_phase(const char *glider_name,
                         const char *neighbor,
                         int phase,
                         size_t *out_len);
```

`glider_name` 是 catalog 名称, 如 `"A"`, `"C2"`, `"Ebar"`, `"Bhat"`。`neighbor` 是 Appendix A parenthesized neighbor; 无 neighbor 传 `NULL`。`phase` 为 `1..4`, 对应 `f1_1..f4_1`。成功返回只读 bit string, 缺 row 或参数非法返回 `NULL`。

```c
size_t len = 0;
const char *bits = glider_phase("C2", "A", 1, &len);
```

### `glider_phase_emit`

```c
int glider_phase_emit(uint8_t *out, size_t pos, size_t buf_len,
                      const char *glider_name, const char *neighbor,
                      int phase, size_t *written_out);
```

把 phase bits 写入 `out[pos..]`。返回 `0` 成功, `1` 表示参数或 catalog row 不存在, `2` 表示 buffer 不足。

```c
uint8_t cells[128] = {0};
size_t written = 0;
int rc = glider_phase_emit(cells, 32, 128, "Ebar", "A", 1, &written);
```

## `encoder/cook_encode.h`

Paper anchor: Cook 2009 §1.4 block compiler; Cook 2004 leader / ossifier / data block construction.

### `CyclicTagInput`

```c
typedef struct {
    uint8_t **productions;
    size_t *prod_lens;
    size_t num_productions;
    uint8_t *initial_tape;
    size_t tape_len;
} CyclicTagInput;
```

`productions` / `prod_lens` / `num_productions` 描述 appendants, `initial_tape` / `tape_len` 描述 cyclic-tag 初始 tape。

### `cook_encode_phase_exact`

```c
int cook_encode_phase_exact(const CyclicTagInput *ct,
                            uint8_t *out,
                            size_t out_cap,
                            size_t *written_out);
```

把 cyclic-tag input 编成 Rule 110 initial row。返回 `COOK_ENCODE_PHASE_EXACT_OK`, `COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING`, `COOK_ENCODE_PHASE_EXACT_INVALID_INPUT`, `COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER`, 或 `COOK_ENCODE_PHASE_EXACT_LAYOUT_OVERFLOW`。

```c
CyclicTagInput ct = {prods, lens, 1, tape, 1};
size_t written = 0;
int rc = cook_encode_phase_exact(&ct, cells, cells_cap, &written);
```

## `encoder/cook_decode.h`

Paper anchor: Cook 2004 `C2 18/10/14` tape spacing; Cook 2009 central tape recipe.

### `cook_decode_output`

```c
int cook_decode_output(const uint8_t *evolved_row,
                       size_t len,
                       char *out_buf,
                       size_t buf_size);
```

从演化 row 解码 output window。返回 `COOK_DECODE_OK`, `COOK_DECODE_INVALID_INPUT`, `COOK_DECODE_NO_OUTPUT`, 或 `COOK_DECODE_OUTPUT_TRUNCATED`。

```c
char decoded[64];
int rc = cook_decode_output(cells, written, decoded, sizeof(decoded));
```

## `encoder/cook_detect.h`

Paper anchor: Martinez 2007 phase rows and period / displacement table; Cook 2004 glider tracking geometry.

### `GliderHit`

```c
typedef struct {
    const char *name;
    const char *neighbor;
    int phase;
    int displacement;
    size_t initial_position;
    size_t final_position;
} GliderHit;
```

字段记录 catalog identity、tracked displacement、初始位置和末端位置。

### `cook_detect_gliders`

```c
int cook_detect_gliders(const uint8_t *initial_row,
                        size_t initial_len,
                        size_t total_steps,
                        GliderHit *hits_out,
                        size_t hits_cap);
```

检测 glider hits。`hits_cap == 0` 时 `hits_out` 可为 `NULL`。返回非负 hit 数；`-1` 表示参数或分配失败。

```c
GliderHit hits[16];
int n = cook_detect_gliders(cells, written, 256, hits, 16);
```

## `encoder/cook_collisions.h`

Paper anchor: Martinez 2012 Table 1 / Table 2 soliton and collision rows.

### Collision lookup accessors

```c
const char *cook_collision_lookup(const char *glider_left,
                                  const char *glider_right,
                                  int ether_gap);
size_t cook_collision_lookup_count(void);
const char *cook_collision_lookup_left(size_t index);
const char *cook_collision_lookup_right(size_t index);
int cook_collision_lookup_gap(size_t index);
const char *cook_collision_lookup_result(size_t index);
```

`cook_collision_lookup` 成功返回 product string, 未命中返回 `NULL`。Indexed accessor 越界时 string accessor 返回 `NULL`, gap accessor 返回 `0`。

```c
const char *result = cook_collision_lookup("F(H,f1_1)", "Bbar(C,f1_1)", 1);
for (size_t i = 0; i < cook_collision_lookup_count(); i++) {
    const char *left = cook_collision_lookup_left(i);
    const char *right = cook_collision_lookup_right(i);
    int gap = cook_collision_lookup_gap(i);
    const char *out = cook_collision_lookup_result(i);
}
```

## `tests/manifest_runner.h`

Paper anchor: BEDC finite witness discipline; Cook 2009 cyclic tag and Rule 110 substrate route.

### CT program accessor

```c
int mr_load_ct_program(const char *manifest_path, MrCtProgram *out);
void mr_free_ct_program(MrCtProgram *m);
```

加载 `.ct` manifest 的 productions。`mr_load_ct_program` 成功返回 `0`, 失败返回 `-1`。

```c
MrCtProgram prog;
if (mr_load_ct_program("manifests/mark/msame_refl.enum.ct", &prog) == 0) {
    mr_free_ct_program(&prog);
}
```

### Manifest runners

```c
MrResult mr_run_ct_manifest(const char *manifest_path,
                            const char *input_bits,
                            const char *expected_final_tape,
                            size_t max_steps);
MrResult mr_run_r110_manifest(const char *manifest_path,
                              size_t max_diff_cells);
```

返回 `MR_PASS`, `MR_FAIL_HALT_REASON`, `MR_FAIL_TAPE_MISMATCH`, 或 `MR_FAIL_LOAD`。

```c
MrResult a = mr_run_ct_manifest("manifests/mark/msame_refl.enum.ct",
                                "011011", "", 200);
MrResult b = mr_run_r110_manifest("manifests/mark/msame_refl.r110.ct", 0);
```
