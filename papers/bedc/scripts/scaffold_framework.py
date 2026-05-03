#!/usr/bin/env python3
"""Generate framework stubs for missing concrete-instance namecert chapters.

Produces a paper-only skeleton (chapter, label, intro paragraph, two section
headers) for each entry in CATALOG. Also emits the list of \\input lines for
main.tex and the list of \\newcommand declarations for any preamble macros
that do not yet exist.
"""

import pathlib
import re

ROOT = pathlib.Path("/Users/auric/newmath/papers/bedc")
DEST = ROOT / "parts" / "concrete_instances"
PREAMBLE = ROOT / "preamble.tex"
MAIN = ROOT / "main.tex"

CATALOG = [
    # (number, file_slug, macro, intro_paragraph)
    (56, "magma", "MagmaUp",
     "The magma interface $\\MagmaUp$ packages a carrier endowed with a single binary operation, with no associativity, identity, or inverse demands. It is the smallest algebraic naming certificate above the inductive carriers of \\autoref{ch:concrete-instances-bool-namecert}--\\autoref{ch:concrete-instances-list-namecert} and the entry point of the algebraic ladder culminating in $\\NameCert_{\\FieldUp}$ (\\autoref{ch:concrete-instances-field-namecert})."),
    (57, "semigroup", "SemigroupUp",
     "The semigroup interface $\\SemigroupUp$ adds associativity to $\\MagmaUp$ (\\autoref{ch:concrete-instances-magma-namecert}). It sits between the magma layer and $\\NameCert_{\\MonoidUp}$ (\\autoref{ch:concrete-instances-monoid-namecert}), exposing the closure law that distinguishes free semigroups from arbitrary binary structures."),
    (58, "subgroup", "SubgroupUp",
     "The subgroup interface $\\SubgroupUp$ packages a subset of a group carrier closed under the group operation, identity, and inverse. It depends on $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert}) and is the first sub-object construction in BEDC, prerequisite to the quotient and ideal certificates that follow."),
    (59, "ideal", "IdealUp",
     "The ideal interface $\\IdealUp$ packages a sub-rng of a ring carrier closed under multiplication by every ambient ring element. It depends on $\\NameCert_{\\RingUp}$ (\\autoref{ch:concrete-instances-ring-namecert}) and supplies the kernel object for the quotient-ring construction $\\NameCert_{\\QuotientRingUp}$ (\\autoref{ch:concrete-instances-quotientring-namecert})."),
    (60, "quotientgroup", "QuotientGroupUp",
     "The quotient-group interface $\\QuotientGroupUp$ packages the carrier of cosets of a normal subgroup of a group. It depends on $\\NameCert_{\\SubgroupUp}$ (\\autoref{ch:concrete-instances-subgroup-namecert}) plus the normality witness, and produces a $\\psame$-classifier on cosets without invoking host-level $\\Quot$-soundness."),
    (61, "quotientring", "QuotientRingUp",
     "The quotient-ring interface $\\QuotientRingUp$ packages the carrier of cosets of an ideal in a ring. It depends on $\\NameCert_{\\IdealUp}$ (\\autoref{ch:concrete-instances-ideal-namecert}) and lifts $\\NameCert_{\\QuotientGroupUp}$ (\\autoref{ch:concrete-instances-quotientgroup-namecert}) to the multiplicative structure."),
    (62, "determinant", "DeterminantUp",
     "The determinant interface $\\DeterminantUp$ packages the alternating multilinear form on square matrices that detects invertibility. It depends on $\\NameCert_{\\MatrixUp}$ (\\autoref{ch:concrete-instances-matrix-namecert}) and $\\NameCert_{\\CommRingUp}$ (\\autoref{ch:concrete-instances-commring-namecert}), and supplies the invariant used by the eigenvalue and characteristic-polynomial certificates."),
    (63, "eigen", "EigenUp",
     "The eigen-pair interface $\\EigenUp$ packages an eigenvalue / eigenvector pair $(\\lambda, v)$ for a linear endomorphism. It depends on $\\NameCert_{\\LinearMapUp}$ (\\autoref{ch:concrete-instances-linearmap-namecert}) and $\\NameCert_{\\DeterminantUp}$ (\\autoref{ch:concrete-instances-determinant-namecert}), with $\\lambda$ certified as a root of the characteristic polynomial."),
    (64, "innerproduct", "InnerProductUp",
     "The inner-product interface $\\InnerProductUp$ packages a vector space together with a constructive sesquilinear form satisfying conjugate symmetry, linearity, and positive definiteness. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}) and is the direct prerequisite for the Hilbert certificate $\\NameCert_{\\HilbertUp}$."),
    (65, "tensorproduct", "TensorProductUp",
     "The tensor-product interface $\\TensorProductUp$ packages the universal bilinear factorization of two module carriers. It depends on $\\NameCert_{\\ModuleUp}$ (\\autoref{ch:concrete-instances-module-namecert}) and supplies the multilinear data on which higher tensor algebras and exterior powers are built."),
    (66, "topology", "TopologyUp",
     "The topology interface $\\TopologyUp$ packages a carrier with a family of open subsets closed under finite intersections and arbitrary unions, certified by an explicit indexing of opens. It generalises $\\NameCert_{\\MetricSpaceUp}$ (\\autoref{ch:concrete-instances-metric-namecert}) by dropping the located-distance requirement and supplies the substrate for $\\NameCert_{\\BanachUp}$, $\\NameCert_{\\ManifoldUp}$, and the topological side of $\\NameCert_{\\ComplexTopologyUp}$ (\\autoref{ch:concrete-instances-complex-topology-namecert})."),
    (67, "norm", "NormUp",
     "The norm interface $\\NormUp$ packages a vector-space carrier with a constructive non-negative real-valued norm satisfying positive definiteness, absolute homogeneity, and the triangle inequality. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}) and $\\NameCert_{\\RealUp}$ (\\autoref{ch:concrete-instances-real-namecert}), and is the immediate prerequisite for $\\NameCert_{\\BanachUp}$."),
    (68, "banach", "BanachUp",
     "The Banach-space interface $\\BanachUp$ packages a normed vector space carrier together with a regular Cauchy completeness witness in the metric induced by the norm. It depends on $\\NameCert_{\\NormUp}$ (\\autoref{ch:concrete-instances-norm-namecert}) and the real-completeness capstone (\\autoref{ch:capstones-real-completeness}), and supplies the substrate for $\\NameCert_{\\HilbertUp}$ and the operator certificates downstream."),
    (69, "hilbert", "HilbertUp",
     "The Hilbert-space interface $\\HilbertUp$ packages a Banach space whose norm is induced by an inner product. It depends on $\\NameCert_{\\InnerProductUp}$ (\\autoref{ch:concrete-instances-innerproduct-namecert}) and $\\NameCert_{\\BanachUp}$ (\\autoref{ch:concrete-instances-banach-namecert}), and is the substrate for the spectral and orthogonal-decomposition certificates of functional analysis."),
    (70, "measure", "MeasureUp",
     "The measure interface $\\MeasureUp$ packages a carrier with a constructive $\\sigma$-additive non-negative real-valued set function on a designated $\\sigma$-algebra of measurable subsets. It depends on $\\NameCert_{\\RealUp}$ (\\autoref{ch:concrete-instances-real-namecert}) and supplies the substrate for the integral certificate $\\NameCert_{\\IntegralUp}$ (\\autoref{ch:concrete-instances-integral-namecert})."),
    (71, "filter", "FilterUp",
     "The filter interface $\\FilterUp$ packages a non-empty upward-closed family of subsets of a carrier closed under finite intersections. It supplies the structural substrate for convergence and limit notions independent of metric data, and is the constructive analogue of mathlib-style \\texttt{Filter} for the BEDC topology and analysis layers."),
    (72, "functionalanalysis", "FunctionalAnalysisUp",
     "The functional-analysis interface $\\FunctionalAnalysisUp$ collects the bounded-linear-operator and dual-space certificates over $\\NameCert_{\\BanachUp}$ (\\autoref{ch:concrete-instances-banach-namecert}) and $\\NameCert_{\\HilbertUp}$ (\\autoref{ch:concrete-instances-hilbert-namecert}). It packages the operator norm, adjoints, and compactness witnesses required by the spectral, semigroup, and PDE certificates downstream."),
    (73, "completion", "CompletionUp",
     "The completion interface $\\CompletionUp$ packages the universal regular-Cauchy completion of a metric naming certificate. It depends on $\\NameCert_{\\MetricSpaceUp}$ (\\autoref{ch:concrete-instances-metric-namecert}) and the real-completeness capstone (\\autoref{ch:capstones-real-completeness}), generalising the $\\RatUp \\to \\RealUp$ construction to arbitrary located metric carriers."),
    (74, "manifold", "ManifoldUp",
     "The manifold interface $\\ManifoldUp$ packages a topological carrier with a finite atlas of charts into $(\\RealUp)^n$ whose transition maps are constructively smooth. It depends on $\\NameCert_{\\TopologyUp}$ (\\autoref{ch:concrete-instances-topology-namecert}) and the real-analytic certificate (\\autoref{ch:concrete-instances-real-analytic-namecert}), and supplies the substrate for the bundle and de~Rham certificates."),
    (75, "bundle", "BundleUp",
     "The bundle interface $\\BundleUp$ packages a fibred carrier $E \\to B$ with locally trivial fibres of a fixed model type. It depends on $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}) for the base and total-space topology, and supplies the substrate for the tangent, cotangent, and frame bundles."),
    (76, "homology", "HomologyUp",
     "The homology interface $\\HomologyUp$ packages a chain complex over an abelian-group carrier together with the kernel/image quotients computing the homology groups. It depends on $\\NameCert_{\\AbGroupUp}$ (\\autoref{ch:concrete-instances-abgroup-namecert}) and $\\NameCert_{\\QuotientGroupUp}$ (\\autoref{ch:concrete-instances-quotientgroup-namecert}), and is the constructive substrate for both singular and simplicial homology."),
    (77, "cohomology", "CohomologyUp",
     "The cohomology interface $\\CohomologyUp$ packages a cochain complex with the dual kernel/image quotients computing cohomology groups. It depends on $\\NameCert_{\\HomologyUp}$ (\\autoref{ch:concrete-instances-homology-namecert}) and supplies the structural substrate for de~Rham, sheaf, and \\v{C}ech cohomology certificates."),
    (78, "padic", "PadicUp",
     "The $p$-adic interface $\\PadicUp$ packages the carrier of regular Cauchy sequences over $\\NameCert_{\\RatUp}$ (\\autoref{ch:concrete-instances-rat-namecert}) under the $p$-adic absolute value, indexed by a prime $p$ from $\\NameCert_{\\PrimeUp}$ (\\autoref{ch:concrete-instances-prime-namecert}). It is the non-archimedean sibling of $\\NameCert_{\\RealUp}$ (\\autoref{ch:concrete-instances-real-namecert})."),
    (79, "adele", "AdeleUp",
     "The adele interface $\\AdeleUp$ packages the restricted product of $\\NameCert_{\\RealUp}$ and $\\NameCert_{\\PadicUp}$ over all primes $p$. It depends on $\\NameCert_{\\PadicUp}$ (\\autoref{ch:concrete-instances-padic-namecert}) and supplies the global object on which automorphic and L-function certificates are built."),
    (80, "modn", "ModNUp",
     "The modular-arithmetic interface $\\ModNUp$ packages the carrier of integers modulo a positive natural $n$. It depends on $\\NameCert_{\\IntUp}$ (\\autoref{ch:concrete-instances-int-namecert}) and is the canonical instance of $\\NameCert_{\\QuotientRingUp}$ (\\autoref{ch:concrete-instances-quotientring-namecert}) at the ideal $n\\mathbb{Z}$."),
    (81, "lfunction", "LFunctionUp",
     "The L-function interface $\\LFunctionUp$ packages a Dirichlet series whose coefficients arise from a fixed character or Galois representation, together with the analytic continuation and functional-equation witnesses. It depends on $\\NameCert_{\\DirichletSeriesUp}$ (\\autoref{ch:concrete-instances-dirichlet-series-namecert}) and is the abstract pattern instantiated by the Riemann zeta certificate $\\NameCert_{\\ZetaBasicUp}$ (\\autoref{ch:concrete-instances-zeta-basic-namecert})."),
    (82, "automorphic", "AutomorphicUp",
     "The automorphic-form interface $\\AutomorphicUp$ packages a function on $\\NameCert_{\\AdeleUp}$ (\\autoref{ch:concrete-instances-adele-namecert}) invariant under a discrete subgroup action and satisfying the constructive growth conditions. It supplies the substrate connecting representations of the adelic group to L-functions in the Langlands programme."),
    (83, "catlimit", "CatLimitUp",
     "The categorical-limit interface $\\CatLimitUp$ packages a cone over a diagram in a $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}) certified universal among all such cones. It depends on $\\NameCert_{\\FunctorUp}$ (\\autoref{ch:concrete-instances-functor-namecert}) and is dual to $\\NameCert_{\\CatColimitUp}$ (\\autoref{ch:concrete-instances-catcolimit-namecert})."),
    (84, "catcolimit", "CatColimitUp",
     "The categorical-colimit interface $\\CatColimitUp$ packages a cocone over a diagram certified couniversal among all such cocones. It depends on $\\NameCert_{\\FunctorUp}$ (\\autoref{ch:concrete-instances-functor-namecert}) and is dual to $\\NameCert_{\\CatLimitUp}$ (\\autoref{ch:concrete-instances-catlimit-namecert})."),
    (85, "adjunction", "AdjunctionUp",
     "The adjunction interface $\\AdjunctionUp$ packages a pair of functors $F \\dashv G$ between two categories together with the natural-isomorphism witness on hom-sets. It depends on $\\NameCert_{\\FunctorUp}$ (\\autoref{ch:concrete-instances-functor-namecert}) and $\\NameCert_{\\NatTransUp}$ (\\autoref{ch:concrete-instances-nattrans-namecert}), and is the canonical structure underlying free/forgetful and Galois-style correspondences."),
    (86, "monad", "MonadUp",
     "The monad interface $\\MonadUp$ packages an endofunctor on a category with unit and multiplication natural transformations satisfying the monad laws. It depends on $\\NameCert_{\\NatTransUp}$ (\\autoref{ch:concrete-instances-nattrans-namecert}) and $\\NameCert_{\\AdjunctionUp}$ (\\autoref{ch:concrete-instances-adjunction-namecert}), and supplies the substrate for algebraic theories and computational effect models."),
    (87, "yoneda", "YonedaUp",
     "The Yoneda interface $\\YonedaUp$ packages, for each object of a category, the representable functor and the natural-isomorphism witness of the Yoneda lemma. It depends on $\\NameCert_{\\FunctorUp}$ (\\autoref{ch:concrete-instances-functor-namecert}) and $\\NameCert_{\\NatTransUp}$ (\\autoref{ch:concrete-instances-nattrans-namecert}), supplying the embedding into presheaf categories."),
    (88, "equivcat", "EquivCatUp",
     "The categorical-equivalence interface $\\EquivCatUp$ packages a pair of functors that are mutually quasi-inverse together with the natural-isomorphism witnesses. It depends on $\\NameCert_{\\AdjunctionUp}$ (\\autoref{ch:concrete-instances-adjunction-namecert}) and $\\NameCert_{\\NatTransUp}$ (\\autoref{ch:concrete-instances-nattrans-namecert}), and is the structural notion of sameness for $\\NameCert_{\\CategoryUp}$ instances."),
    (89, "set", "SetUp",
     "The set interface $\\SetUp$ packages a carrier together with a $\\psame$-classifier interpretable as set-membership equality. It is the type-layer counterpart of $\\NameCert_{\\PreorderUp}$ (\\autoref{ch:concrete-instances-preorder-namecert}) at the discrete level, and the substrate for $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert}) and $\\NameCert_{\\SubtypeUp}$ (\\autoref{ch:concrete-instances-subtype-namecert})."),
    (90, "finset", "FinSetUp",
     "The finite-set interface $\\FinSetUp$ packages a $\\NameCert_{\\SetUp}$ together with a finite enumeration witness via $\\NameCert_{\\ListUp}$ (\\autoref{ch:concrete-instances-list-namecert}). It depends on $\\NameCert_{\\SetUp}$ (\\autoref{ch:concrete-instances-set-namecert}) and is the substrate for combinatorial certificates such as $\\NameCert_{\\PermutationUp}$ and $\\NameCert_{\\GraphUp}$."),
    (91, "subtype", "SubtypeUp",
     "The subtype interface $\\SubtypeUp$ packages the carrier of elements of a parent $\\NameCert_{\\SetUp}$ satisfying a decidable predicate. It depends on $\\NameCert_{\\SetUp}$ (\\autoref{ch:concrete-instances-set-namecert}) and supplies the kernel-licit refinement type used throughout the algebra ladder for sub-objects."),
    (92, "empty", "EmptyUp",
     "The empty-type interface $\\EmptyUp$ packages the unique naming certificate over the inductive carrier with no constructors. It is the initial object in the category of naming certificates and supplies the canonical absurdity witness for refutation patterns."),
    (93, "unit", "UnitUp",
     "The unit-type interface $\\UnitUp$ packages the unique naming certificate over the inductive carrier with a single constructor. It is the terminal object in the category of naming certificates and supplies the canonical trivial witness for placeholder constructions."),
    (94, "permutation", "PermutationUp",
     "The permutation interface $\\PermutationUp$ packages the carrier of bijections of a $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert}) onto itself. It supplies the underlying carrier for $\\NameCert_{\\SymGroupUp}$ (\\autoref{ch:concrete-instances-symgroup-namecert}) and the action data for combinatorial group-theoretic certificates."),
    (95, "symgroup", "SymGroupUp",
     "The symmetric-group interface $\\SymGroupUp$ packages the group structure on $\\NameCert_{\\PermutationUp}$ (\\autoref{ch:concrete-instances-permutation-namecert}) under composition. It is a canonical instance of $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert}) and the substrate for representation-theoretic certificates."),
    (96, "graph", "GraphUp",
     "The graph interface $\\GraphUp$ packages a vertex carrier from $\\NameCert_{\\SetUp}$ (\\autoref{ch:concrete-instances-set-namecert}) together with a binary edge relation. It supplies the substrate for $\\NameCert_{\\TreeUp}$ (\\autoref{ch:concrete-instances-tree-namecert}) and for combinatorial structures such as posets viewed as DAGs."),
    (97, "tree", "TreeUp",
     "The tree interface $\\TreeUp$ packages a connected acyclic $\\NameCert_{\\GraphUp}$ (\\autoref{ch:concrete-instances-graph-namecert}) together with a designated root or root-free witness. It is the constructive substrate for inductive carriers and for the syntactic representation of derivations."),
    (98, "seq", "SeqUp",
     "The sequence interface $\\SeqUp$ packages a function $\\NatUp \\to A$ for a fixed naming-certificate carrier $A$, together with a regularity or boundedness modulus. It depends on $\\NameCert_{\\NatUp}$ (\\autoref{ch:concrete-instances-nat-namecert}) and is the general substrate for $\\NameCert_{\\SeriesUp}$, $\\NameCert_{\\ConvergenceRadiusUp}$, and the analytic-limit certificates."),
    (99, "series", "SeriesUp",
     "The series interface $\\SeriesUp$ packages the partial-sum sequence of a $\\NameCert_{\\SeqUp}$ (\\autoref{ch:concrete-instances-seq-namecert}) over an additive carrier together with explicit convergence moduli. It is the real-and-general counterpart of $\\NameCert_{\\ComplexSeriesUp}$ (\\autoref{ch:concrete-instances-complex-series-namecert})."),
    (100, "derivative", "DerivativeUp",
     "The derivative interface $\\DerivativeUp$ packages the constructive pointwise derivative of a function between metric carriers, with explicit modulus relating $\\varepsilon$ to the difference-quotient tolerance. It is the real and general counterpart of $\\NameCert_{\\ComplexDiffUp}$ (\\autoref{ch:concrete-instances-complex-diff-namecert})."),
    (101, "integral", "IntegralUp",
     "The integral interface $\\IntegralUp$ packages a measure-respecting integration operation on suitable function carriers over $\\NameCert_{\\MeasureUp}$ (\\autoref{ch:concrete-instances-measure-namecert}). It generalises the contour integral $\\NameCert_{\\ContourUp}$ (\\autoref{ch:concrete-instances-contour-integral}) to Riemann/Lebesgue settings on real and abstract carriers."),
    (102, "fourier", "FourierUp",
     "The Fourier interface $\\FourierUp$ packages the constructive Fourier series and transform of suitable functions on $\\NameCert_{\\SOneUp}$ (\\autoref{ch:concrete-instances-s1-namecert}) and $\\NameCert_{\\RealUp}$. It depends on $\\NameCert_{\\InnerProductUp}$ (\\autoref{ch:concrete-instances-innerproduct-namecert}) and $\\NameCert_{\\IntegralUp}$ (\\autoref{ch:concrete-instances-integral-namecert})."),
    (103, "residue", "ResidueUp",
     "The residue interface $\\ResidueUp$ packages the residue at an isolated singularity of a holomorphic function and the residue-theorem witness relating contour integrals to residue sums. It depends on $\\NameCert_{\\HolomorphicUp}$ (\\autoref{ch:concrete-instances-holomorphic-namecert}) and $\\NameCert_{\\ContourUp}$ (\\autoref{ch:concrete-instances-contour-integral})."),
    (104, "streamname", "StreamNameUp",
     "The stream-name interface $\\StreamNameUp$ packages an abstract sequential carrier underlying the Bishop-style L10 real-number construction. It is the lowest-level data on which $\\NameCert_{\\TotallyBoundedUp}$, $\\NameCert_{\\CompleteMetricUp}$, $\\NameCert_{\\CompactMetricUp}$, and $\\NameCert_{\\ContinuousMapUp}$ are built."),
    (105, "totallybounded", "TotallyBoundedUp",
     "The totally-bounded interface $\\TotallyBoundedUp$ packages a metric carrier admitting, for every $\\varepsilon > 0$, an explicit finite $\\varepsilon$-net. It depends on $\\NameCert_{\\MetricSpaceUp}$ (\\autoref{ch:concrete-instances-metric-namecert}) and is the prerequisite for $\\NameCert_{\\CompactMetricUp}$ (\\autoref{ch:concrete-instances-compactmetric-namecert})."),
    (106, "completemetric", "CompleteMetricUp",
     "The complete-metric interface $\\CompleteMetricUp$ packages a metric carrier in which every regular Cauchy sequence converges to an explicit limit with explicit modulus. It is the L10 sub-milestone certified by the real-completeness capstone (\\autoref{ch:capstones-real-completeness}) and the substrate for $\\NameCert_{\\BanachUp}$."),
    (107, "compactmetric", "CompactMetricUp",
     "The compact-metric interface $\\CompactMetricUp$ packages a metric carrier that is both totally bounded and complete in the senses of $\\NameCert_{\\TotallyBoundedUp}$ (\\autoref{ch:concrete-instances-totallybounded-namecert}) and $\\NameCert_{\\CompleteMetricUp}$ (\\autoref{ch:concrete-instances-completemetric-namecert}). It is the metric form of compactness used by the Heine--Cantor capstone (\\autoref{ch:capstones-compact-uniform-continuity})."),
    (108, "continuousmap", "ContinuousMapUp",
     "The continuous-map interface $\\ContinuousMapUp$ packages a function between metric carriers together with a pointwise modulus of continuity. It depends on $\\NameCert_{\\MetricSpaceUp}$ (\\autoref{ch:concrete-instances-metric-namecert}) and lifts $\\NameCert_{\\ContinuousFunctionUp}$ (\\autoref{ch:concrete-instances-continuous-namecert}) to general L10 metric carriers."),
    (109, "eqtype", "EqUp",
     "The equality-type interface $\\EqUp$ packages the constructive identity type over a carrier, with reflexivity as the sole constructor and explicit transport for kernel-licit substitution. It supplies the foundational equality layer underlying every $\\psame$ classifier."),
    (110, "funcobj", "FuncUp",
     "The function-object interface $\\FuncUp$ packages the carrier of functions $A \\to B$ between two naming certificates, together with the pointwise $\\hsame$-respecting structure. It supplies the substrate for $\\NameCert_{\\LinearMapUp}$ (\\autoref{ch:concrete-instances-linearmap-namecert}) and $\\NameCert_{\\ContinuousMapUp}$ (\\autoref{ch:concrete-instances-continuousmap-namecert}) as restrictions of the general function object."),
]

TEMPLATE = """\\chapter{{A Concrete Naming Certificate for $\\{macro}$}}
\\label{{ch:concrete-instances-{slug}-namecert}}

{intro}

\\section{{Carrier definition}}
\\label{{sec:{slug}-carrier}}

\\section{{The certificate}}
\\label{{sec:{slug}-certificate}}
"""


def existing_macros():
    text = PREAMBLE.read_text()
    return set(re.findall(r"\\newcommand\{\\([A-Z][A-Za-z]*Up)\}", text))


def main():
    have = existing_macros()
    missing = []
    inputs = []
    for num, slug, macro, intro in CATALOG:
        path = DEST / f"{num}_{slug}_namecert_construction.tex"
        path.write_text(TEMPLATE.format(macro=macro, slug=slug, intro=intro))
        inputs.append(f"\\input{{parts/concrete_instances/{num}_{slug}_namecert_construction.tex}}")
        if macro not in have:
            missing.append(macro)
    print("WROTE", len(CATALOG), "files into", DEST)
    print()
    print("=== INPUT LINES (append to main.tex Concrete Instances part) ===")
    for line in inputs:
        print(line)
    print()
    print("=== MISSING MACROS (add to preamble.tex) ===")
    for m in missing:
        # Convert MacroUp -> mathsf{Body}^uparrow
        body = m[:-2]  # strip "Up"
        print(f"\\newcommand{{\\{m}}}{{\\mathsf{{{body}}}^{{\\uparrow}}}}")


if __name__ == "__main__":
    main()
