import BEDC.Derived.CauchyUp.CoreNameCert

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyL10SiblingDependencyRoute [AskSetup] [PackageSetup]
    {stream dyadic regSeq realSeal l10Window toleranceRead regularRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regSeq ->
          UnaryHistory realSeal ->
            Cont stream dyadic l10Window ->
              Cont l10Window regSeq toleranceRead ->
                Cont toleranceRead realSeal regularRead ->
                  Cont regularRead realSeal publicRead ->
                    PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row stream ∨ hsame row dyadic ∨ hsame row regSeq ∨
                              hsame row realSeal ∨ hsame row publicRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory l10Window ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory regularRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro streamUnary dyadicUnary regSeqUnary realSealUnary streamDyadicRoute
    windowRegSeqRoute toleranceRealRoute regularRealRoute publicPkg
  have windowUnary : UnaryHistory l10Window :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary regSeqUnary windowRegSeqRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceUnary realSealUnary toleranceRealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed regularUnary realSealUnary regularRealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row dyadic ∨ hsame row regSeq ∨
              hsame row realSeal ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, regularUnary, publicUnary⟩

theorem CauchyRouteRegSeqRatTailInversion [AskSetup] [PackageSetup]
    {stream dyadic regSeq realSeal l10Window toleranceRead regularRead approximation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regSeq ->
          UnaryHistory realSeal ->
            Cont stream dyadic l10Window ->
              Cont l10Window regSeq toleranceRead ->
                Cont toleranceRead realSeal regularRead ->
                  Cont regularRead realSeal approximation ->
                    PkgSig bundle approximation pkg ->
                      UnaryHistory l10Window ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory approximation ∧
                          Cont stream dyadic l10Window ∧
                            Cont l10Window regSeq toleranceRead ∧
                              Cont toleranceRead realSeal regularRead ∧
                                Cont regularRead realSeal approximation ∧
                                  PkgSig bundle approximation pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro streamUnary dyadicUnary regSeqUnary realSealUnary streamDyadicRoute
    windowRegSeqRoute toleranceRealRoute regularApproxRoute approximationPkg
  have windowUnary : UnaryHistory l10Window :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary regSeqUnary windowRegSeqRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceUnary realSealUnary toleranceRealRoute
  have approximationUnary : UnaryHistory approximation :=
    unary_cont_closed regularUnary realSealUnary regularApproxRoute
  exact
    ⟨windowUnary, toleranceUnary, regularUnary, approximationUnary, streamDyadicRoute,
      windowRegSeqRoute, toleranceRealRoute, regularApproxRoute, approximationPkg⟩

end BEDC.Derived.CauchyUp
