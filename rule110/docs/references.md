# Rule 110 / Cook construction / Cyclic tag research references

下载链接清单. PDF 不入仓库 — 本地存到 `rule110/ignores/` (.gitignore 排除).

## 一手原 (Cook + Martinez)

- Cook 2004, "Universality in Elementary Cellular Automata", Complex Systems 15.
  http://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf
  https://www.dna.caltech.edu/courses/cs191/paperscs191/Cook_Rule110_Full_Unpublished.pdf

- Martinez et al. 2007, "Determining a regular language by glider-based structures called phases f_i_1 in Rule 110", arXiv.
  https://arxiv.org/abs/0706.3348
  https://arxiv.org/pdf/0706.3348

- Martinez/Adamatzky/Chen/Chua 2012, "On Soliton Collisions between Localizations in Complex ECAs: Rules 54 and 110 and Beyond", Complex Systems 21.2.2.
  https://content.wolfram.com/sites/13/2018/12/21-2-2.pdf
  https://doi.org/10.25088/ComplexSystems.21.2.117

## 显式编译器 (语义 round-trip 关键)

- "A Concrete View of Rule 110 Computation", arXiv 0906.3248.
  显式 Turing machine → Rule 110 初始 state compiler. 可能正是 semantic round-trip 缺的环节.
  https://arxiv.org/abs/0906.3248
  https://arxiv.org/pdf/0906.3248

- "A Particular Universal Cellular Automaton", arXiv 0906.3227.
  https://arxiv.org/abs/0906.3227
  https://arxiv.org/pdf/0906.3227

## Neary-Woods 时间复杂度 (Rule 110 polynomial 仿真)

- Neary/Woods, "Small weakly universal Turing machines", arXiv 0707.4489.
  https://arxiv.org/abs/0707.4489
  https://arxiv.org/pdf/0707.4489

- Related complexity, arXiv 1110.2230.
  https://arxiv.org/pdf/1110.2230

## Glider 动力学 / 碰撞 / 逻辑门

- Martinez/Adamatzky, "Logical Gates via Glider Collisions", arXiv 1803.05496.
  https://arxiv.org/pdf/1803.05496

- "A Computation in a Cellular Automaton Collider Rule 110", arXiv 1609.05240.
  其引用指向 listPhasesR110.txt.
  https://arxiv.org/abs/1609.05240
  https://arxiv.org/pdf/1609.05240
  https://ar5iv.labs.arxiv.org/html/1609.05240

- Martinez/Adamatzky, "Cellular Automaton Supercolliders", arXiv 1105.4332.
  https://arxiv.org/pdf/1105.4332

## 循环标签系统复杂度

- Ninagawa/Martinez, "Complexity Analysis in Cyclic Tag System Emulated by Rule 110", arXiv 1307.7951.
  Lempel-Ziv complexity stepwise decline analysis.
  https://arxiv.org/abs/1307.7951
  https://arxiv.org/pdf/1307.7951

- "Undecidability in binary tag systems and the Post correspondence problem", arXiv 1312.6700.
  https://arxiv.org/abs/1312.6700
  https://arxiv.org/pdf/1312.6700

## Class III/IV 分类

- "Computation and Universality: Class IV versus Class III Cellular Automata", arXiv 1304.1242.
  https://arxiv.org/pdf/1304.1242

- "Wolfram's Classification and Computation in CA Classes III and IV", arXiv 1208.2456.
  https://arxiv.org/pdf/1208.2456

## Glider gun (2D, 周边参考)

- "Minimal Glider-Gun in a 2D Cellular Automaton", arXiv 1709.02655.
  https://arxiv.org/abs/1709.02655
  https://arxiv.org/pdf/1709.02655

## Martinez 个人站资源

- http://uncomp.uwe.ac.uk/genaro/Rule110.html (rule 110 主页, 现在 404)
- http://uncomp.uwe.ac.uk/genaro/rule110/listPhasesR110.txt (phase catalog 原 URL, 现在 404 — 内容在 `rule110/encoder/listPhasesR110.txt` 仓库保留)
- https://www.comunidad.escom.ipn.mx/genaro/rule110/glidersRule110.html (镜像, 仍可访问)

## 本地下载脚本

```bash
cd rule110/ignores
bash ../docs/fetch_references.sh
```

如果将来需要重新下载, fetch_references.sh 会按上述顺序 curl 所有 PDF.
