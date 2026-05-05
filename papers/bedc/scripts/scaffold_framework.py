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
    (111, "riemannianmetric", "RiemannianMetricUp",
     "The Riemannian-metric interface $\\RiemannianMetricUp$ packages a smooth field of positive-definite inner products on the tangent fibres of a manifold carrier. It depends on $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}) and $\\NameCert_{\\InnerProductUp}$ (\\autoref{ch:concrete-instances-innerproduct-namecert}), and supplies the metric substrate for length, geodesic, and curvature certificates."),
    (112, "connection", "ConnectionUp",
     "The connection interface $\\ConnectionUp$ packages a covariant derivative on a fibre bundle, with linearity in the section argument and the Leibniz rule against scalar functions. It depends on $\\NameCert_{\\BundleUp}$ (\\autoref{ch:concrete-instances-bundle-namecert}) and $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}), and supplies the parallel-transport and curvature substrate."),
    (113, "curvature", "CurvatureUp",
     "The curvature interface $\\CurvatureUp$ packages the antisymmetric bracket of a connection, certifying the Bianchi identities and the tensorial behaviour under section change. It depends on $\\NameCert_{\\ConnectionUp}$ (\\autoref{ch:concrete-instances-connection-namecert}) and supplies the local invariants on which Riemannian and gauge-field certificates rest."),
    (114, "diffform", "DiffFormUp",
     "The differential-form interface $\\DiffFormUp$ packages the carrier of antisymmetric multilinear maps on the tangent bundle of a manifold, together with the wedge product. It depends on $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}) and $\\NameCert_{\\TensorProductUp}$ (\\autoref{ch:concrete-instances-tensorproduct-namecert}), and is the substrate for the de~Rham complex."),
    (115, "deRham", "DeRhamUp",
     "The de~Rham interface $\\DeRhamUp$ packages the exterior-derivative chain complex on differential forms, certifying $d^2 = 0$ and $\\hsame$-stability. It depends on $\\NameCert_{\\DiffFormUp}$ (\\autoref{ch:concrete-instances-diffform-namecert}) and $\\NameCert_{\\CohomologyUp}$ (\\autoref{ch:concrete-instances-cohomology-namecert}), and supplies the de~Rham cohomology of a manifold."),
    (116, "symplectic", "SymplecticUp",
     "The symplectic-structure interface $\\SymplecticUp$ packages a closed nondegenerate $2$-form on an even-dimensional manifold carrier. It depends on $\\NameCert_{\\DiffFormUp}$ (\\autoref{ch:concrete-instances-diffform-namecert}) and $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}), and is the substrate for Hamiltonian dynamics and Poisson-bracket certificates."),
    (117, "contact", "ContactUp",
     "The contact-structure interface $\\ContactUp$ packages a maximally nonintegrable hyperplane field on an odd-dimensional manifold carrier, recorded as a $1$-form whose top-degree wedge is nondegenerate. It depends on $\\NameCert_{\\DiffFormUp}$ (\\autoref{ch:concrete-instances-diffform-namecert}) and $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert})."),
    (118, "liegroup", "LieGroupUp",
     "The Lie-group interface $\\LieGroupUp$ packages a group carrier whose underlying set is a manifold and whose multiplication and inverse are constructively smooth. It depends on $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert}) and $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}), and is the substrate for representation, exponential, and root-system certificates."),
    (119, "liealgebra", "LieAlgebraUp",
     "The Lie-algebra interface $\\LieAlgebraUp$ packages a vector-space carrier endowed with an antisymmetric bilinear bracket satisfying the Jacobi identity. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}), and is both the tangent-space-at-identity datum of a Lie group and the algebraic object on which root-system certificates are built."),
    (120, "expmap", "ExpMapUp",
     "The exponential-map interface $\\ExpMapUp$ packages the canonical map $\\mathfrak{g} \\to G$ from the Lie algebra to the Lie group of a connected Lie-group carrier. It depends on $\\NameCert_{\\LieGroupUp}$ (\\autoref{ch:concrete-instances-liegroup-namecert}) and $\\NameCert_{\\LieAlgebraUp}$ (\\autoref{ch:concrete-instances-liealgebra-namecert})."),
    (121, "adjointrep", "AdjointRepUp",
     "The adjoint-representation interface $\\AdjointRepUp$ packages the conjugation action $\\mathrm{Ad}\\colon G \\to \\mathrm{Aut}(\\mathfrak{g})$ together with its differential $\\mathrm{ad}$. It depends on $\\NameCert_{\\LieGroupUp}$ (\\autoref{ch:concrete-instances-liegroup-namecert}) and $\\NameCert_{\\LieAlgebraUp}$ (\\autoref{ch:concrete-instances-liealgebra-namecert})."),
    (122, "rootsystem", "RootSystemUp",
     "The root-system interface $\\RootSystemUp$ packages a finite set of nonzero vectors in a finite-dimensional inner-product space closed under the reflections they generate, with integer Cartan pairings. It depends on $\\NameCert_{\\InnerProductUp}$ (\\autoref{ch:concrete-instances-innerproduct-namecert}) and $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert}), and is the combinatorial backbone of semisimple Lie-algebra classification."),
    (123, "weylgroup", "WeylGroupUp",
     "The Weyl-group interface $\\WeylGroupUp$ packages the finite reflection group generated by the simple roots of a root system. It depends on $\\NameCert_{\\RootSystemUp}$ (\\autoref{ch:concrete-instances-rootsystem-namecert}) and $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert}), and is the discrete symmetry datum on which character-theoretic certificates rest."),
    (124, "bilinform", "BilinFormUp",
     "The bilinear-form interface $\\BilinFormUp$ packages a bilinear pairing on a module carrier together with its symmetry, antisymmetry, and nondegeneracy classifiers. It depends on $\\NameCert_{\\ModuleUp}$ (\\autoref{ch:concrete-instances-module-namecert}) and $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}), and is the universal datum from which inner products, symplectic forms, and Clifford algebras are licensed."),
    (125, "clifford", "CliffordUp",
     "The Clifford-algebra interface $\\CliffordUp$ packages the universal associative algebra generated by a vector-space carrier and a quadratic form $q$, modulo the relation $v \\cdot v = q(v)$. It depends on $\\NameCert_{\\TensorProductUp}$ (\\autoref{ch:concrete-instances-tensorproduct-namecert}) and $\\NameCert_{\\BilinFormUp}$ (\\autoref{ch:concrete-instances-bilinform-namecert}), and is the substrate for the Spin and Pin certificates."),
    (126, "spingroup", "SpinGroupUp",
     "The Spin-group interface $\\SpinGroupUp$ packages the connected double cover of the orthogonal group as a subgroup of the Clifford-algebra units. It depends on $\\NameCert_{\\CliffordUp}$ (\\autoref{ch:concrete-instances-clifford-namecert}) and $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert})."),
    (127, "pingroup", "PinGroupUp",
     "The Pin-group interface $\\PinGroupUp$ packages the double cover of the full orthogonal group, extending Spin by a reflection generator. It depends on $\\NameCert_{\\SpinGroupUp}$ (\\autoref{ch:concrete-instances-spingroup-namecert}) and $\\NameCert_{\\CliffordUp}$ (\\autoref{ch:concrete-instances-clifford-namecert})."),
    (128, "presheaf", "PreSheafUp",
     "The presheaf interface $\\PreSheafUp$ packages a contravariant functor from the open-sets category of a topological carrier to a target category, with restriction maps respecting composition and identity. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}) and $\\NameCert_{\\FunctorUp}$ (\\autoref{ch:concrete-instances-functor-namecert})."),
    (129, "sheaf", "SheafUp",
     "The sheaf interface $\\SheafUp$ packages a presheaf satisfying the locality and gluing axioms over open covers. It depends on $\\NameCert_{\\PreSheafUp}$ (\\autoref{ch:concrete-instances-presheaf-namecert}) and $\\NameCert_{\\TopologyUp}$ (\\autoref{ch:concrete-instances-topology-namecert}), and is the substrate for ringed-space and scheme certificates."),
    (130, "ringedspace", "RingedSpaceUp",
     "The ringed-space interface $\\RingedSpaceUp$ packages a topological carrier with a sheaf of commutative rings on it, certifying that stalks form local rings. It depends on $\\NameCert_{\\SheafUp}$ (\\autoref{ch:concrete-instances-sheaf-namecert}) and $\\NameCert_{\\CommRingUp}$ (\\autoref{ch:concrete-instances-commring-namecert})."),
    (131, "scheme", "SchemeUp",
     "The scheme interface $\\SchemeUp$ packages a locally ringed space that admits an open cover by spectra of commutative rings. It depends on $\\NameCert_{\\RingedSpaceUp}$ (\\autoref{ch:concrete-instances-ringedspace-namecert}) and $\\NameCert_{\\CommRingUp}$ (\\autoref{ch:concrete-instances-commring-namecert}), and is the substrate for affine and projective variety certificates."),
    (132, "affinevar", "AffineVarUp",
     "The affine-variety interface $\\AffineVarUp$ packages the zero-locus of a finite system of polynomial equations in the affine $n$-space of a commutative-ring carrier. It depends on $\\NameCert_{\\CommRingUp}$ (\\autoref{ch:concrete-instances-commring-namecert}) and $\\NameCert_{\\PolynomialUp}$ (\\autoref{ch:concrete-instances-polynomial-namecert})."),
    (133, "projectivevar", "ProjectiveVarUp",
     "The projective-variety interface $\\ProjectiveVarUp$ packages the zero-locus of a homogeneous polynomial ideal in the projective $n$-space of a commutative-ring carrier. It depends on $\\NameCert_{\\AffineVarUp}$ (\\autoref{ch:concrete-instances-affinevar-namecert}) and $\\NameCert_{\\PolynomialUp}$ (\\autoref{ch:concrete-instances-polynomial-namecert})."),
    (134, "homotopy", "HomotopyUp",
     "The homotopy interface $\\HomotopyUp$ packages the equivalence-of-paths relation between continuous maps under a continuous deformation parameter. It depends on $\\NameCert_{\\ContinuousMapUp}$ (\\autoref{ch:concrete-instances-continuousmap-namecert}) and $\\NameCert_{\\IntervalUp}$ (\\autoref{ch:concrete-instances-interval-namecert}), and is the substrate for fundamental-group and higher-homotopy certificates."),
    (135, "simplicialset", "SimplicialSetUp",
     "The simplicial-set interface $\\SimplicialSetUp$ packages a contravariant functor from the simplex category $\\Delta$ to a certified set carrier, with face and degeneracy operators satisfying the simplicial identities. It depends on $\\NameCert_{\\FunctorUp}$ (\\autoref{ch:concrete-instances-functor-namecert}) and $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert})."),
    (136, "modelcat", "ModelCatUp",
     "The model-category interface $\\ModelCatUp$ packages a category carrier with three distinguished classes of morphisms (cofibrations, fibrations, weak equivalences) satisfying lifting and factorisation axioms. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}), and is the homotopy-theoretic substrate beneath higher-category certificates."),
    (137, "infcat", "InfCatUp",
     "The $\\infty$-category interface $\\InfCatUp$ packages a simplicial-set carrier satisfying the inner-horn lifting condition (a quasicategory). It depends on $\\NameCert_{\\SimplicialSetUp}$ (\\autoref{ch:concrete-instances-simplicialset-namecert}) and $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert})."),
    (138, "derivedcat", "DerivedCatUp",
     "The derived-category interface $\\DerivedCatUp$ packages the localisation of a chain-complex category at quasi-isomorphisms. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}) and $\\NameCert_{\\CohomologyUp}$ (\\autoref{ch:concrete-instances-cohomology-namecert})."),
    (139, "fieldext", "FieldExtUp",
     "The field-extension interface $\\FieldExtUp$ packages an embedding of one field carrier into another, recording the larger field as a vector space over the smaller. It depends on $\\NameCert_{\\FieldUp}$ (\\autoref{ch:concrete-instances-field-namecert}) and $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}), and is the substrate for Galois, separable, and algebraic-closure certificates."),
    (140, "algclosure", "AlgClosureUp",
     "The algebraic-closure interface $\\AlgClosureUp$ packages a field extension in which every nonconstant polynomial over the base field has a root. It depends on $\\NameCert_{\\FieldExtUp}$ (\\autoref{ch:concrete-instances-fieldext-namecert}) and $\\NameCert_{\\PolynomialUp}$ (\\autoref{ch:concrete-instances-polynomial-namecert})."),
    (141, "galoisext", "GaloisExtUp",
     "The Galois-extension interface $\\GaloisExtUp$ packages a normal and separable field extension. It depends on $\\NameCert_{\\FieldExtUp}$ (\\autoref{ch:concrete-instances-fieldext-namecert}) and $\\NameCert_{\\SeparableExtUp}$ (\\autoref{ch:concrete-instances-separableext-namecert})."),
    (142, "galoisgroup", "GaloisGroupUp",
     "The Galois-group interface $\\GaloisGroupUp$ packages the group of field automorphisms of a Galois extension fixing the base field pointwise. It depends on $\\NameCert_{\\GaloisExtUp}$ (\\autoref{ch:concrete-instances-galoisext-namecert}) and $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert})."),
    (143, "splittingfield", "SplittingFieldUp",
     "The splitting-field interface $\\SplittingFieldUp$ packages the smallest field extension over which a given polynomial factors into linear terms. It depends on $\\NameCert_{\\FieldExtUp}$ (\\autoref{ch:concrete-instances-fieldext-namecert}) and $\\NameCert_{\\PolynomialUp}$ (\\autoref{ch:concrete-instances-polynomial-namecert})."),
    (144, "separableext", "SeparableExtUp",
     "The separable-extension interface $\\SeparableExtUp$ packages a field extension whose minimal polynomials all have simple roots. It depends on $\\NameCert_{\\FieldExtUp}$ (\\autoref{ch:concrete-instances-fieldext-namecert}) and $\\NameCert_{\\PolynomialUp}$ (\\autoref{ch:concrete-instances-polynomial-namecert})."),
    (145, "transcendence", "TranscendenceUp",
     "The transcendence interface $\\TranscendenceUp$ packages the supremum of cardinalities of algebraically independent subsets of a field extension. It depends on $\\NameCert_{\\FieldExtUp}$ (\\autoref{ch:concrete-instances-fieldext-namecert})."),
    (146, "numfield", "NumFieldUp",
     "The number-field interface $\\NumFieldUp$ packages a finite field extension of the rational-number certificate. It depends on $\\NameCert_{\\FieldExtUp}$ (\\autoref{ch:concrete-instances-fieldext-namecert}) and $\\NameCert_{\\RatUp}$ (\\autoref{ch:concrete-instances-rat-namecert})."),
    (147, "ringofintegers", "RingOfIntegersUp",
     "The ring-of-integers interface $\\RingOfIntegersUp$ packages the integral closure of $\\IntUp$ inside a number-field carrier. It depends on $\\NameCert_{\\NumFieldUp}$ (\\autoref{ch:concrete-instances-numfield-namecert}) and $\\NameCert_{\\IntUp}$ (\\autoref{ch:concrete-instances-int-namecert})."),
    (148, "idealclass", "IdealClassUp",
     "The ideal-class interface $\\IdealClassUp$ packages the quotient group of fractional ideals modulo principal ideals in a Dedekind domain. It depends on $\\NameCert_{\\DedekindUp}$ (\\autoref{ch:concrete-instances-dedekind-namecert}) and $\\NameCert_{\\QuotientGroupUp}$ (\\autoref{ch:concrete-instances-quotientgroup-namecert})."),
    (149, "dirichletunit", "DirichletUnitUp",
     "The Dirichlet-unit interface $\\DirichletUnitUp$ packages the structure of the unit group of a ring of integers as a finitely generated abelian group of rank $r_1 + r_2 - 1$. It depends on $\\NameCert_{\\RingOfIntegersUp}$ (\\autoref{ch:concrete-instances-ringofintegers-namecert}) and $\\NameCert_{\\AbGroupUp}$ (\\autoref{ch:concrete-instances-abgroup-namecert})."),
    (150, "dedekind", "DedekindUp",
     "The Dedekind-domain interface $\\DedekindUp$ packages an integrally closed Noetherian commutative domain in which every nonzero prime ideal is maximal. It depends on $\\NameCert_{\\CommRingUp}$ (\\autoref{ch:concrete-instances-commring-namecert}) and $\\NameCert_{\\IdealUp}$ (\\autoref{ch:concrete-instances-ideal-namecert})."),
    (151, "localfield", "LocalFieldUp",
     "The local-field interface $\\LocalFieldUp$ packages a complete discretely valued field with finite residue field. It depends on $\\NameCert_{\\FieldUp}$ (\\autoref{ch:concrete-instances-field-namecert}) and $\\NameCert_{\\PadicUp}$ (\\autoref{ch:concrete-instances-padic-namecert})."),
    (152, "cyclotomic", "CyclotomicUp",
     "The cyclotomic-field interface $\\CyclotomicUp$ packages the splitting field of $X^n - 1$ over the rational-number certificate. It depends on $\\NameCert_{\\NumFieldUp}$ (\\autoref{ch:concrete-instances-numfield-namecert}) and $\\NameCert_{\\SplittingFieldUp}$ (\\autoref{ch:concrete-instances-splittingfield-namecert})."),
    (153, "ellipticcurve", "EllipticCurveUp",
     "The elliptic-curve interface $\\EllipticCurveUp$ packages a smooth projective genus-one curve over a field carrier together with a chosen base point. It depends on $\\NameCert_{\\ProjectiveVarUp}$ (\\autoref{ch:concrete-instances-projectivevar-namecert}) and $\\NameCert_{\\FieldUp}$ (\\autoref{ch:concrete-instances-field-namecert})."),
    (154, "abeliancat", "AbelianCatUp",
     "The abelian-category interface $\\AbelianCatUp$ packages an additive category in which every morphism has a kernel and cokernel and the canonical epi-mono factorisation is an isomorphism. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}) and $\\NameCert_{\\AbGroupUp}$ (\\autoref{ch:concrete-instances-abgroup-namecert})."),
    (155, "derivedfunctor", "DerivedFunctorUp",
     "The derived-functor interface $\\DerivedFunctorUp$ packages the right- or left-derived $R^iF$ / $L_iF$ of an additive functor between abelian categories. It depends on $\\NameCert_{\\AbelianCatUp}$ (\\autoref{ch:concrete-instances-abeliancat-namecert}) and $\\NameCert_{\\HomologyUp}$ (\\autoref{ch:concrete-instances-homology-namecert})."),
    (156, "spectralseq", "SpectralSeqUp",
     "The spectral-sequence interface $\\SpectralSeqUp$ packages a sequence of bigraded objects with differentials whose successive cohomologies converge to a target. It depends on $\\NameCert_{\\HomologyUp}$ (\\autoref{ch:concrete-instances-homology-namecert}) and $\\NameCert_{\\AbelianCatUp}$ (\\autoref{ch:concrete-instances-abeliancat-namecert})."),
    (157, "triangulatedcat", "TriangulatedCatUp",
     "The triangulated-category interface $\\TriangulatedCatUp$ packages an additive category with a translation autoequivalence and a class of distinguished triangles satisfying the octahedral axiom. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}) and $\\NameCert_{\\DerivedCatUp}$ (\\autoref{ch:concrete-instances-derivedcat-namecert})."),
    (158, "hopfalg", "HopfAlgUp",
     "The Hopf-algebra interface $\\HopfAlgUp$ packages a bialgebra carrier together with an antipode satisfying the convolution-inverse axiom. It depends on $\\NameCert_{\\RingUp}$ (\\autoref{ch:concrete-instances-ring-namecert}) and $\\NameCert_{\\TensorProductUp}$ (\\autoref{ch:concrete-instances-tensorproduct-namecert})."),
    (159, "monoidalcat", "MonoidalCatUp",
     "The monoidal-category interface $\\MonoidalCatUp$ packages a category with a tensor-product bifunctor, unit object, and coherent associator and unitor isomorphisms. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert})."),
    (160, "enrichedcat", "EnrichedCatUp",
     "The enriched-category interface $\\EnrichedCatUp$ packages a collection of objects with hom-objects valued in a fixed monoidal category, with composition and identity morphisms in that monoidal category. It depends on $\\NameCert_{\\MonoidalCatUp}$ (\\autoref{ch:concrete-instances-monoidalcat-namecert}) and $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert})."),
    (161, "topos", "ToposUp",
     "The topos interface $\\ToposUp$ packages a category with finite limits, exponentials, and a subobject classifier. It depends on $\\NameCert_{\\CategoryUp}$ (\\autoref{ch:concrete-instances-category-namecert}) and $\\NameCert_{\\SheafUp}$ (\\autoref{ch:concrete-instances-sheaf-namecert}), and is the substrate for sheaf-of-sets cohomology and internal logic."),
    (162, "probspace", "ProbSpaceUp",
     "The probability-space interface $\\ProbSpaceUp$ packages a measure space whose total measure is the unit. It depends on $\\NameCert_{\\MeasureUp}$ (\\autoref{ch:concrete-instances-measure-namecert}) and $\\NameCert_{\\RealUp}$ (\\autoref{ch:concrete-instances-real-namecert})."),
    (163, "randomvar", "RandomVarUp",
     "The random-variable interface $\\RandomVarUp$ packages a measurable function from a probability space to a target measure space. It depends on $\\NameCert_{\\ProbSpaceUp}$ (\\autoref{ch:concrete-instances-probspace-namecert}) and $\\NameCert_{\\MeasureUp}$ (\\autoref{ch:concrete-instances-measure-namecert})."),
    (164, "distribution", "DistributionUp",
     "The distribution interface $\\DistributionUp$ packages the pushforward measure of a random variable on its target space. It depends on $\\NameCert_{\\RandomVarUp}$ (\\autoref{ch:concrete-instances-randomvar-namecert}) and $\\NameCert_{\\MeasureUp}$ (\\autoref{ch:concrete-instances-measure-namecert})."),
    (165, "independence", "IndependenceUp",
     "The independence interface $\\IndependenceUp$ packages the property that the joint distribution of a finite family of random variables factors as the product of marginals. It depends on $\\NameCert_{\\RandomVarUp}$ (\\autoref{ch:concrete-instances-randomvar-namecert}) and $\\NameCert_{\\DistributionUp}$ (\\autoref{ch:concrete-instances-distribution-namecert})."),
    (166, "condexp", "CondExpUp",
     "The conditional-expectation interface $\\CondExpUp$ packages the $L^2$ projection of an integrable random variable onto the subspace of functions measurable with respect to a sub-$\\sigma$-algebra. It depends on $\\NameCert_{\\RandomVarUp}$ (\\autoref{ch:concrete-instances-randomvar-namecert}) and $\\NameCert_{\\HilbertUp}$ (\\autoref{ch:concrete-instances-hilbert-namecert})."),
    (167, "markovchain", "MarkovChainUp",
     "The Markov-chain interface $\\MarkovChainUp$ packages a sequence of random variables in which the conditional distribution of each step depends only on the previous step. It depends on $\\NameCert_{\\RandomVarUp}$ (\\autoref{ch:concrete-instances-randomvar-namecert}) and $\\NameCert_{\\DistributionUp}$ (\\autoref{ch:concrete-instances-distribution-namecert})."),
    (168, "martingale", "MartingaleUp",
     "The martingale interface $\\MartingaleUp$ packages an adapted sequence of integrable random variables whose conditional expectation at each step is the previous value. It depends on $\\NameCert_{\\RandomVarUp}$ (\\autoref{ch:concrete-instances-randomvar-namecert}) and $\\NameCert_{\\CondExpUp}$ (\\autoref{ch:concrete-instances-condexp-namecert})."),
    (169, "brownian", "BrownianUp",
     "The Brownian-motion interface $\\BrownianUp$ packages a continuous-time stochastic process with independent normally distributed increments and continuous sample paths. It depends on $\\NameCert_{\\MartingaleUp}$ (\\autoref{ch:concrete-instances-martingale-namecert}) and $\\NameCert_{\\ContinuousMapUp}$ (\\autoref{ch:concrete-instances-continuousmap-namecert})."),
    (170, "entropy", "EntropyUp",
     "The entropy interface $\\EntropyUp$ packages the Shannon entropy $-\\sum p_i \\log p_i$ of a discrete distribution and the differential entropy $-\\int f \\log f$ of a continuous one. It depends on $\\NameCert_{\\DistributionUp}$ (\\autoref{ch:concrete-instances-distribution-namecert}) and $\\NameCert_{\\IntegralUp}$ (\\autoref{ch:concrete-instances-integral-namecert})."),
    (171, "ode", "OdeUp",
     "The ordinary-differential-equation interface $\\OdeUp$ packages a system $\\dot x = F(t, x)$ together with the local existence and uniqueness data on Lipschitz vector fields. It depends on $\\NameCert_{\\DerivativeUp}$ (\\autoref{ch:concrete-instances-derivative-namecert}) and $\\NameCert_{\\BanachUp}$ (\\autoref{ch:concrete-instances-banach-namecert})."),
    (172, "pde", "PdeUp",
     "The partial-differential-equation interface $\\PdeUp$ packages a relation among partial derivatives of a function on a manifold carrier together with classification by order, type, and boundary data. It depends on $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}) and $\\NameCert_{\\DerivativeUp}$ (\\autoref{ch:concrete-instances-derivative-namecert})."),
    (173, "dynsystem", "DynSystemUp",
     "The dynamical-system interface $\\DynSystemUp$ packages a one-parameter family of self-maps of a phase-space carrier satisfying the flow axioms. It depends on $\\NameCert_{\\ManifoldUp}$ (\\autoref{ch:concrete-instances-manifold-namecert}) and $\\NameCert_{\\OdeUp}$ (\\autoref{ch:concrete-instances-ode-namecert})."),
    (174, "ergodic", "ErgodicUp",
     "The ergodic-theory interface $\\ErgodicUp$ packages a measure-preserving transformation together with the ergodic decomposition of its invariant subspaces. It depends on $\\NameCert_{\\DynSystemUp}$ (\\autoref{ch:concrete-instances-dynsystem-namecert}) and $\\NameCert_{\\MeasureUp}$ (\\autoref{ch:concrete-instances-measure-namecert})."),
    (175, "firstorder", "FirstOrderUp",
     "The first-order-logic interface $\\FirstOrderUp$ packages a signature of relation and function symbols, a set of formulas, and a deduction calculus together with the soundness and completeness data. It depends on $\\NameCert_{\\SetUp}$ (\\autoref{ch:concrete-instances-set-namecert}) and $\\NameCert_{\\TreeUp}$ (\\autoref{ch:concrete-instances-tree-namecert})."),
    (176, "modeltheory", "ModelTheoryUp",
     "The model-theory interface $\\ModelTheoryUp$ packages a structure for a first-order signature, satisfaction of formulas, elementary equivalence, and elementary substructures. It depends on $\\NameCert_{\\FirstOrderUp}$ (\\autoref{ch:concrete-instances-firstorder-namecert})."),
    (177, "computable", "ComputableUp",
     "The computable-function interface $\\ComputableUp$ packages partial functions $\\mathbb{N} \\to \\mathbb{N}$ defined by Turing-machine simulation up to time-step bounds. It depends on $\\NameCert_{\\NatUp}$ (\\autoref{ch:concrete-instances-nat-namecert}) and $\\NameCert_{\\SeqUp}$ (\\autoref{ch:concrete-instances-seq-namecert})."),
    (178, "lambdacalc", "LambdaCalcUp",
     "The lambda-calculus interface $\\LambdaCalcUp$ packages the inductive carrier of $\\lambda$-terms together with $\\beta$-reduction, $\\alpha$-equivalence, and a stability classifier under capture-avoiding substitution. It depends on $\\NameCert_{\\TreeUp}$ (\\autoref{ch:concrete-instances-tree-namecert}) and $\\NameCert_{\\NatUp}$ (\\autoref{ch:concrete-instances-nat-namecert})."),
    (179, "partition", "PartitionUp",
     "The integer-partition interface $\\PartitionUp$ packages weakly decreasing sequences of positive integers summing to a fixed integer, together with the Young-diagram interpretation. It depends on $\\NameCert_{\\NatUp}$ (\\autoref{ch:concrete-instances-nat-namecert}) and $\\NameCert_{\\ListUp}$ (\\autoref{ch:concrete-instances-list-namecert})."),
    (180, "matroid", "MatroidUp",
     "The matroid interface $\\MatroidUp$ packages a finite ground set with a family of subsets (independent sets) closed under taking subsets and satisfying the exchange axiom. It depends on $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert}) and $\\NameCert_{\\LatticeUp}$ (\\autoref{ch:concrete-instances-lattice-namecert})."),
    (181, "ramsey", "RamseyUp",
     "The Ramsey-theory interface $\\RamseyUp$ packages, for every finite colouring of the $r$-element subsets of a sufficiently large finite set, a monochromatic subset of bounded size. It depends on $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert}) and $\\NameCert_{\\GraphUp}$ (\\autoref{ch:concrete-instances-graph-namecert})."),
    (182, "topgroup", "TopGroupUp",
     "The topological-group interface $\\TopGroupUp$ packages a group carrier with a topology making multiplication and inversion continuous. It depends on $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert}) and $\\NameCert_{\\TopologyUp}$ (\\autoref{ch:concrete-instances-topology-namecert})."),
    (183, "topvecspace", "TopVecSpaceUp",
     "The topological-vector-space interface $\\TopVecSpaceUp$ packages a vector-space carrier with a Hausdorff topology making addition and scalar multiplication continuous. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}) and $\\NameCert_{\\TopologyUp}$ (\\autoref{ch:concrete-instances-topology-namecert})."),
    (184, "affinespace", "AffineSpaceUp",
     "The affine-space interface $\\AffineSpaceUp$ packages a torsor over a vector-space carrier: a set with a free transitive action of vector translations. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}) and $\\NameCert_{\\GroupUp}$ (\\autoref{ch:concrete-instances-group-namecert})."),
    (185, "projectivespace", "ProjectiveSpaceUp",
     "The projective-space interface $\\ProjectiveSpaceUp$ packages the quotient of a punctured vector-space carrier by the scaling action of the underlying field's multiplicative group. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}) and $\\NameCert_{\\FieldUp}$ (\\autoref{ch:concrete-instances-field-namecert})."),
    (186, "convexset", "ConvexSetUp",
     "The convex-set interface $\\ConvexSetUp$ packages a subset of a vector-space carrier closed under affine combinations with nonnegative coefficients summing to one. It depends on $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert}) and $\\NameCert_{\\AffineSpaceUp}$ (\\autoref{ch:concrete-instances-affinespace-namecert})."),
    (187, "polytope", "PolytopeUp",
     "The polytope interface $\\PolytopeUp$ packages a bounded convex set in a finite-dimensional vector-space carrier presented as the intersection of finitely many half-spaces, with vertex, edge, and face combinatorial structure. It depends on $\\NameCert_{\\ConvexSetUp}$ (\\autoref{ch:concrete-instances-convexset-namecert}) and $\\NameCert_{\\FinSetUp}$ (\\autoref{ch:concrete-instances-finset-namecert})."),
    (188, "vectorbundle", "VectorBundleUp",
     "The vector-bundle interface $\\VectorBundleUp$ packages a fibre bundle whose fibres are vector spaces and whose transition maps are linear. It depends on $\\NameCert_{\\BundleUp}$ (\\autoref{ch:concrete-instances-bundle-namecert}) and $\\NameCert_{\\VecSpaceUp}$ (\\autoref{ch:concrete-instances-vecspace-namecert})."),
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
    wrote = 0
    for num, slug, macro, intro in CATALOG:
        path = DEST / f"{num}_{slug}_namecert_construction.tex"
        if not path.exists():
            path.write_text(TEMPLATE.format(macro=macro, slug=slug, intro=intro))
            wrote += 1
        inputs.append(f"\\input{{parts/concrete_instances/{num}_{slug}_namecert_construction.tex}}")
        if macro not in have:
            missing.append(macro)
    print("WROTE", wrote, "new files (skipped", len(CATALOG) - wrote, "existing) into", DEST)
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
