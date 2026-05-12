#!/usr/bin/env python3
"""One-shot: write wiki_en/wiki_zh URLs into per-term glossary TOMLs.

Skips BEDC project-internal terms (no Wikipedia page exists).
Only writes when a real Wikipedia article is known to exist.
ZH URL is included only when the Chinese Wikipedia entry is known
to exist; missing zh URL keeps just wiki_en.

Run from repo root:
    python3 tools/patch_glossary_wiki.py
"""

from __future__ import annotations

import sys
from pathlib import Path
from urllib.parse import quote

sys.path.insert(0, str(Path(__file__).resolve().parent))

from _glossary_loader import load_glossary, emit_entry, GLOSSARY_DIR  # type: ignore


# en_title and zh_title are the article slugs after /wiki/, in their native
# scripts (we URL-encode at write time). zh_title = "" means no Chinese wiki.
WIKI: dict[str, tuple[str, str]] = {
    "abeliancat":          ("Abelian_category", "阿贝尔范畴"),
    "abelruffini":         ("Abel–Ruffini_theorem", "阿贝尔-鲁菲尼定理"),
    "abgroup":             ("Abelian_group", "阿贝尔群"),
    "add":                 ("Addition", "加法"),
    "adele":               ("Adele_ring", "阿代尔环"),
    "adjointrep":          ("Adjoint_representation", "伴随表示"),
    "adjunction":          ("Adjoint_functors", "伴随函子"),
    "affinespace":         ("Affine_space", "仿射空间"),
    "affinevar":           ("Affine_variety", "仿射簇"),
    "algclosure":          ("Algebraic_closure", "代數閉包"),
    "approximation":       ("Approximation_theory", "逼近理论"),
    "atiyahsinger":        ("Atiyah–Singer_index_theorem", "阿蒂亚-辛格指标定理"),
    "automorphic":         ("Automorphic_form", "自守形式"),
    "banach":              ("Banach_space", "巴拿赫空间"),
    "bayesian":            ("Bayesian_inference", "贝叶斯推断"),
    "bessel":              ("Bessel_function", "贝塞尔函数"),
    "bilinform":           ("Bilinear_form", "双线性形式"),
    "bool":                ("Boolean_algebra", "布尔代数"),
    "brownian":            ("Brownian_motion", "布朗运动"),
    "bundle":              ("Fiber_bundle", "纤维丛"),
    "busybeaver":          ("Busy_beaver", "繁忙的海狸"),
    "calculus":            ("Calculus", "微积分学"),
    "catcolimit":          ("Limit_(category_theory)", "极限_(范畴论)"),
    "category":            ("Category_(mathematics)", "范畴_(数学)"),
    "catlimit":            ("Limit_(category_theory)", "极限_(范畴论)"),
    "charactertheory":     ("Character_theory", "特征标理论"),
    "chernweil":           ("Chern–Weil_homomorphism", ""),
    "circle":              ("Circle", "圆"),
    "classfield":          ("Class_field_theory", "类域论"),
    "clebschgordan":       ("Clebsch–Gordan_coefficients", "克莱布希-高登系数"),
    "clifford":            ("Clifford_algebra", "克利福德代数"),
    "cohomology":          ("Cohomology", "上同调"),
    "commring":            ("Commutative_ring", "交换环"),
    "compact":             ("Compact_space", "紧空间"),
    "compactmetric":       ("Compact_space", "紧空间"),
    "completemetric":      ("Complete_metric_space", "完备度量空间"),
    "completion":          ("Completion_(metric_space)", "完備化"),
    "complex":             ("Complex_number", "复数_(数学)"),
    "complexanalytic":     ("Holomorphic_function", "全纯函数"),
    "complexdiff":         ("Cauchy–Riemann_equations", "柯西-黎曼方程"),
    "complexityclass":     ("Complexity_class", "复杂度类"),
    "complexlimit":        ("Limit_of_a_sequence", "数列极限"),
    "complexseries":       ("Series_(mathematics)", "级数"),
    "complextopology":     ("Topology", "拓扑学"),
    "computable":          ("Computable_function", "可计算函数"),
    "condexp":             ("Conditional_expectation", "条件期望"),
    "connection":          ("Connection_(mathematics)", "联络_(数学)"),
    "contact":             ("Contact_geometry", "接触几何"),
    "continuous":          ("Continuous_function", "连续函数"),
    "continuousmap":       ("Continuous_function", "连续函数"),
    "contour":             ("Contour_integration", "围道积分"),
    "convergenceradius":   ("Radius_of_convergence", "收敛半径"),
    "convexset":           ("Convex_set", "凸集"),
    "critstrip":           ("Riemann_hypothesis", "黎曼猜想"),
    "cstaralgebra":        ("C*-algebra", "C*-代数"),
    "curryhoward":         ("Curry–Howard_correspondence", "柯里-霍华德同构"),
    "curvature":           ("Curvature", "曲率"),
    "cyclotomic":          ("Cyclotomic_field", "分圆域"),
    "dedekind":            ("Dedekind_domain", "戴德金整环"),
    "deformquantization":  ("Deformation_quantization", ""),
    "densitymatrix":       ("Density_matrix", "密度矩阵"),
    "derham":              ("De_Rham_cohomology", "德拉姆上同调"),
    "derivative":          ("Derivative", "导数"),
    "derivedcat":          ("Derived_category", "导出范畴"),
    "derivedfunctor":      ("Derived_functor", "导出函子"),
    "determinant":         ("Determinant", "行列式"),
    "diffform":            ("Differential_form", "微分形式"),
    "diffgalois":          ("Differential_Galois_theory", ""),
    "dirichletseries":     ("Dirichlet_series", "狄利克雷级数"),
    "dirichletunit":       ("Dirichlet%27s_unit_theorem", ""),
    "distribution":        ("Distribution_(mathematics)", "广义函数"),
    "dynsystem":           ("Dynamical_system", "动力系统"),
    "eigen":               ("Eigenvalues_and_eigenvectors", "特征向量"),
    "ellipticcurve":       ("Elliptic_curve", "椭圆曲线"),
    "empty":               ("Empty_type", "空类型"),
    "enrichedcat":         ("Enriched_category", ""),
    "entanglement":        ("Quantum_entanglement", "量子纠缠"),
    "entropy":             ("Entropy_(information_theory)", "熵_(信息论)"),
    "eq":                  ("Equality_(mathematics)", "相等"),
    "eqtype":              ("Equality_(mathematics)", "相等"),
    "equivcat":            ("Equivalence_of_categories", "范畴等价"),
    "ergodic":             ("Ergodic_theory", "遍历理论"),
    "errorcode":           ("Error_correction_code", "前向错误更正"),
    "estimator":           ("Estimator", "估计量"),
    "expmap":              ("Exponential_map_(Lie_theory)", "指数映射"),
    "factor":              ("Von_Neumann_algebra#Factors", ""),
    "fft":                 ("Fast_Fourier_transform", "快速傅里叶变换"),
    "field":               ("Field_(mathematics)", "域_(数学)"),
    "fieldext":            ("Field_extension", "域扩张"),
    "filter":              ("Filter_(mathematics)", "滤子_(数学)"),
    "finset":              ("Finite_set", "有限集合"),
    "firstorder":          ("First-order_logic", "一阶逻辑"),
    "fisherinfo":          ("Fisher_information", "费希尔信息"),
    "fold":                ("Fold_(higher-order_function)", "折叠_(高阶函数)"),
    "fourier":             ("Fourier_transform", "傅里叶变换"),
    "fps":                 ("Formal_power_series", "形式幂级数"),
    "func":                ("Function_(mathematics)", "函数"),
    "funcobj":             ("Function_object", "函数对象"),
    "functionalanalysis":  ("Functional_analysis", "泛函分析"),
    "functor":             ("Functor", "函子"),
    "galoisext":           ("Galois_extension", "伽罗瓦扩张"),
    "galoisgroup":         ("Galois_group", "伽罗瓦群"),
    "gamma":               ("Gamma_function", "Γ函数"),
    "gammafunction":       ("Gamma_function", "Γ函数"),
    "gelfandduality":      ("Gelfand_representation", ""),
    "geomquantization":    ("Geometric_quantization", ""),
    "goedelincompleteness":("Gödel%27s_incompleteness_theorems", "哥德尔不完备定理"),
    "graph":               ("Graph_(discrete_mathematics)", "图_(数学)"),
    "group":               ("Group_(mathematics)", "群"),
    "hash":                ("Hash_function", "散列函数"),
    "hilbert":             ("Hilbert_space", "希尔伯特空间"),
    "hodgebridge":         ("Hodge_theory", "霍奇理论"),
    "holomorphic":         ("Holomorphic_function", "全纯函数"),
    "homology":            ("Homology_(mathematics)", "同调"),
    "homotopy":            ("Homotopy", "同伦"),
    "hopfalg":             ("Hopf_algebra", "霍普夫代数"),
    "hypergeometric":      ("Hypergeometric_function", "超几何函数"),
    "hypothesis":          ("Statistical_hypothesis_testing", "假设检验"),
    "ideal":               ("Ideal_(ring_theory)", "理想_(环论)"),
    "idealclass":          ("Ideal_class_group", "理想类群"),
    "independence":        ("Independence_(probability_theory)", "独立_(概率论)"),
    "inducedrep":          ("Induced_representation", ""),
    "infcat":              ("∞-category", "无穷范畴"),
    "innerproduct":        ("Inner_product_space", "内积空间"),
    "int":                 ("Integer", "整数"),
    "integral":            ("Integral", "积分"),
    "interpolation":       ("Interpolation", "插值"),
    "interval":            ("Interval_(mathematics)", "区间"),
    "iwasawa":             ("Iwasawa_theory", "岩泽理论"),
    "jonespolynomial":     ("Jones_polynomial", "琼斯多项式"),
    "knot":                ("Knot_theory", "纽结理论"),
    "kolmogorov":          ("Kolmogorov_complexity", "柯氏复杂性"),
    "koszulduality":       ("Koszul_duality", ""),
    "lambdacalc":          ("Lambda_calculus", "Λ演算"),
    "langlands":           ("Langlands_program", "朗兰兹纲领"),
    "lattice":             ("Lattice_(order)", "格_(序理论)"),
    "lfunction":           ("L-function", "L函数"),
    "liealgebra":          ("Lie_algebra", "李代数"),
    "liegroup":            ("Lie_group", "李群"),
    "limit":               ("Limit_(mathematics)", "极限_(数学)"),
    "linearmap":           ("Linear_map", "线性映射"),
    "list":                ("List_(abstract_data_type)", "列表_(抽象数据类型)"),
    "localfield":          ("Local_field", "局部域"),
    "lpduality":           ("Dual_linear_program", ""),
    "magma":               ("Magma_(algebra)", "原群"),
    "manifold":            ("Manifold", "流形"),
    "mapper":              ("Topological_data_analysis#Mapper", ""),
    "markovchain":         ("Markov_chain", "马尔可夫链"),
    "martingale":          ("Martingale_(probability_theory)", "鞅_(概率论)"),
    "matching":            ("Matching_(graph_theory)", "匹配_(图论)"),
    "matrix":              ("Matrix_(mathematics)", "矩阵"),
    "matroid":             ("Matroid", "拟阵"),
    "measure":             ("Measure_(mathematics)", "测度"),
    "metric":              ("Metric_space", "度量空间"),
    "mirrorsymmetry":      ("Mirror_symmetry_(string_theory)", "镜对称_(弦论)"),
    "modelcat":            ("Model_category", ""),
    "modeltheory":         ("Model_theory", "模型论"),
    "modn":                ("Modular_arithmetic", "模运算"),
    "modularform":         ("Modular_form", "模形式"),
    "module":              ("Module_(mathematics)", "模_(数学)"),
    "monad":               ("Monad_(functional_programming)", "单子_(函数式编程)"),
    "monoid":              ("Monoid", "幺半群"),
    "monoidalcat":         ("Monoidal_category", "幺半范畴"),
    "mul":                 ("Multiplication", "乘法"),
    "nat":                 ("Natural_number", "自然数"),
    "nattrans":            ("Natural_transformation", "自然变换"),
    "networkflow":         ("Flow_network", "流网络"),
    "newtoniteration":     ("Newton%27s_method", "牛顿法"),
    "noethersymmetry":     ("Noether%27s_theorem", "诺特定理"),
    "norm":                ("Normed_vector_space", "赋范向量空间"),
    "nuclear":             ("Nuclear_operator", ""),
    "numfield":            ("Algebraic_number_field", "代数数域"),
    "observable":          ("Observable", "可观察量"),
    "ode":                 ("Ordinary_differential_equation", "常微分方程"),
    "operatorideal":       ("Operator_ideal", ""),
    "option":              ("Option_type", "可空型別"),
    "order":               ("Order_theory", "序理论"),
    "padic":               ("P-adic_number", "P进数"),
    "partition":           ("Partition_(number_theory)", "整数分拆"),
    "pde":                 ("Partial_differential_equation", "偏微分方程"),
    "permutation":         ("Permutation", "排列"),
    "persistenthom":       ("Persistent_homology", ""),
    "pingroup":            ("Pin_group", ""),
    "polynomial":          ("Polynomial", "多项式"),
    "polytope":            ("Polytope", "多胞形"),
    "pontryaginduality":   ("Pontryagin_duality", "庞特里亚金对偶性"),
    "poset":               ("Partially_ordered_set", "偏序关系"),
    "preorder":            ("Preorder", "预序关系"),
    "presheaf":            ("Sheaf_(mathematics)#Presheaves", ""),
    "prime":               ("Prime_number", "素数"),
    "probspace":           ("Probability_space", "概率空间"),
    "prod":                ("Product_type", "积类型"),
    "projectivespace":     ("Projective_space", "射影空间"),
    "projectivevar":       ("Projective_variety", "射影簇"),
    "publickey":           ("Public-key_cryptography", "公开密钥加密"),
    "quadrature":          ("Numerical_integration", "数值积分"),
    "quantumchannel":      ("Quantum_channel", "量子信道"),
    "quantumstate":        ("Quantum_state", "量子态"),
    "quotientgroup":       ("Quotient_group", "商群"),
    "quotientring":        ("Quotient_ring", "商环"),
    "ramsey":              ("Ramsey_theory", "拉姆齐理论"),
    "randomvar":           ("Random_variable", "随机变量"),
    "rat":                 ("Rational_number", "有理数"),
    "real":                ("Real_number", "实数"),
    "realanalytic":        ("Analytic_function", "解析函数"),
    "recursivefn":         ("Recursive_function", "递归函数"),
    "regulator":           ("Regulator_(mathematics)", ""),
    "representationring":  ("Representation_ring", ""),
    "residue":             ("Residue_(complex_analysis)", "留数"),
    "rh":                  ("Riemann_hypothesis", "黎曼猜想"),
    "riemannhilbert":      ("Riemann–Hilbert_correspondence", ""),
    "riemannianmetric":    ("Riemannian_manifold", "黎曼流形"),
    "ring":                ("Ring_(mathematics)", "环_(代数)"),
    "ringedspace":         ("Ringed_space", "环空间"),
    "ringofintegers":      ("Ring_of_integers", "整数环"),
    "rootsystem":          ("Root_system", "根系"),
    "s1":                  ("Circle_group", "圓群"),
    "scheme":              ("Scheme_(mathematics)", "概形"),
    "semigroup":           ("Semigroup", "半群"),
    "separableext":        ("Separable_extension", "可分扩张"),
    "seq":                 ("Sequence", "数列"),
    "series":              ("Series_(mathematics)", "级数"),
    "set":                 ("Set_(mathematics)", "集合_(数学)"),
    "sheaf":               ("Sheaf_(mathematics)", "层_(数学)"),
    "shortestpath":        ("Shortest_path_problem", "最短路问题"),
    "simplicialcomplex":   ("Simplicial_complex", "单纯复形"),
    "simplicialset":       ("Simplicial_set", ""),
    "solvableradicals":    ("Solvable_group", "可解群"),
    "spanningtree":        ("Spanning_tree", "生成树"),
    "spectralseq":         ("Spectral_sequence", "谱序列"),
    "spectraltheorem":     ("Spectral_theorem", "谱定理"),
    "spingroup":           ("Spin_group", "自旋群"),
    "splittingfield":      ("Splitting_field", "分裂域"),
    "stack":               ("Stack_(mathematics)", "代数堆叠"),
    "statmanifold":        ("Information_geometry", "资讯几何学"),
    "stoneduality":        ("Stone_duality", ""),
    "subgroup":            ("Subgroup", "子群"),
    "subtype":             ("Subtyping", "子类型"),
    "sum":                 ("Tagged_union", "标签联合"),
    "symgroup":            ("Symmetric_group", "对称群"),
    "symplectic":          ("Symplectic_geometry", "辛几何"),
    "tannakakrein":        ("Tannaka–Krein_duality", ""),
    "tensorproduct":       ("Tensor_product", "张量积"),
    "thetafunction":       ("Theta_function", "Θ函数"),
    "threemanifold":       ("3-manifold", "三维流形"),
    "topgroup":            ("Topological_group", "拓扑群"),
    "topology":            ("Topological_space", "拓扑空间"),
    "topos":               ("Topos", "拓扑斯"),
    "topvecspace":         ("Topological_vector_space", "拓扑向量空间"),
    "totallybounded":      ("Totally_bounded_space", ""),
    "totalorder":          ("Total_order", "全序关系"),
    "transcendence":       ("Transcendence_degree", "超越次数"),
    "tree":                ("Tree_(graph_theory)", "树_(图论)"),
    "triangulatedcat":     ("Triangulated_category", "三角范畴"),
    "turingmachine":       ("Turing_machine", "图灵机"),
    "unit":                ("Unit_type", "单元类型"),
    "unitarygroup":        ("Unitary_group", "酉群"),
    "vecspace":            ("Vector_space", "向量空间"),
    "vectorbundle":        ("Vector_bundle", "向量丛"),
    "vermamodule":         ("Verma_module", ""),
    "vonneumannalgebra":   ("Von_Neumann_algebra", "冯诺依曼代数"),
    "weylgroup":           ("Weyl_group", "外尔群"),
    "yoneda":              ("Yoneda_lemma", "米田引理"),
    "zeroknowledge":       ("Zero-knowledge_proof", "零知识证明"),
    "zeta":                ("Riemann_zeta_function", "黎曼ζ函数"),
    "zetabasic":           ("Riemann_zeta_function", "黎曼ζ函数"),
    "zetacont":            ("Analytic_continuation", "解析延拓"),
    "zetazeros":           ("Riemann_hypothesis", "黎曼猜想"),
}


def url_en(title: str) -> str:
    return f"https://en.wikipedia.org/wiki/{quote(title, safe='_-%')}"


def url_zh(title: str) -> str:
    return f"https://zh.wikipedia.org/wiki/{quote(title, safe='_-%')}"


def main() -> int:
    data = load_glossary()
    keys = [k for k in data if not k.startswith("_")]
    patched = 0
    for k in keys:
        if k not in WIKI:
            continue
        en_t, zh_t = WIKI[k]
        entry = data[k]
        entry.setdefault("en", {})["wiki"] = url_en(en_t)
        if zh_t:
            entry.setdefault("zh", {})["wiki"] = url_zh(zh_t)
        # Rewrite the TOML for this key
        # Case-insensitive filesystems (macOS) break naive `path.exists()`,
        # so resolve the exact filename by scanning the directory listing
        # and matching the canonical `key = "..."` field inside.
        target = None
        for candidate in GLOSSARY_DIR.glob("*.toml"):
            if candidate.name == "_meta.toml":
                continue
            head = candidate.read_text(encoding="utf-8").splitlines()[0]
            # head looks like: key = 'foo' or key = "foo"
            if head.startswith("key = "):
                lit = head[len("key = "):].strip().strip("'").strip('"')
                if lit == k:
                    target = candidate
                    break
        if target is None:
            print(f"warn: no TOML file for key {k}", file=sys.stderr)
            continue
        target.write_text(emit_entry(k, entry), encoding="utf-8")
        patched += 1
    print(f"patched {patched} / {len(WIKI)} mapped entries; {len(keys)} total keys")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
