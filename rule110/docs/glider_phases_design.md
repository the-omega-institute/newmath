# Glider Phase Lookup Design

`glider_phase` uses the catalog glider name as the primary key, with the
neighbor column reserved for the local phase context shown by the source
catalog.

The Martinez catalog distinguishes `D1` and `D2`, and Cook Figure 5 gives them
different widths. The lookup table therefore registers them as separate glider
names:

```text
glider_phase("D1", "A", 1, &len)
glider_phase("D2", "A", 1, &len)
```

The generic name `D` is not an alias. Keeping `D1` and `D2` explicit avoids
encoding the subindex into neighbor strings such as `1A` or `2A`, and leaves
the neighbor key aligned with the `A`, `B`, and `C` contexts in
`listPhasesR110.txt`.

Catalog aliases are represented by registering each named phase with the same
bit string as its target, for example `D1(B,f4_1)` and `D1(C,f1_1)`.
