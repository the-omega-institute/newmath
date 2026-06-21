import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RealCauchyRateUp : Type where
  | mk : (D S Q R H C P N : BHist) -> RealCauchyRateUp
  deriving DecidableEq

def realCauchyRateFields : RealCauchyRateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyRateUp.mk D S Q R H C P N => [D, S, Q, R, H, C, P, N]

theorem RealCauchyRateCarrier_regular_namecert [AskSetup] [PackageSetup]
    (K : RealCauchyRateUp)
    {D S Q R H C P N toleranceRead windowRead regularRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realCauchyRateFields K = [D, S, Q, R, H, C, P, N] ->
      UnaryHistory D ->
        UnaryHistory S ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory H ->
              UnaryHistory N ->
                Cont D S toleranceRead ->
                  Cont toleranceRead Q windowRead ->
                    Cont windowRead R regularRead ->
                      Cont regularRead H sealRead ->
                        Cont sealRead N namedRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row D ∨ hsame row S ∨ hsame row Q ∨
                                    hsame row R ∨ hsame row H ∨ hsame row N ∨
                                      hsame row toleranceRead ∨ hsame row windowRead ∨
                                        hsame row regularRead ∨ hsame row sealRead ∨
                                          hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont D S toleranceRead ∧
                                    Cont toleranceRead Q windowRead ∧
                                      Cont windowRead R regularRead ∧
                                        Cont regularRead H sealRead ∧
                                          Cont sealRead N namedRead ∧
                                            PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                                UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RealCauchyRateUp realCauchyRateFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsD rowsS rowsQ rowsR rowsH rowsN toleranceRoute windowRoute regularRoute
    sealRoute namedRoute packageRead
  have _acceptedFields : realCauchyRateFields K = [D, S, Q, R, H, C, P, N] := fields
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed rowsD rowsS toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary rowsQ windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rowsR regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary rowsH sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨ hsame row H ∨
              hsame row N ∨ hsame row toleranceRead ∨ hsame row windowRead ∨
                hsame row regularRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S toleranceRead ∧
              Cont toleranceRead Q windowRead ∧ Cont windowRead R regularRead ∧
                Cont regularRead H sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, toleranceRoute, windowRoute, regularRoute, sealRoute, namedRoute,
          packageRead⟩
  }
  exact ⟨cert, toleranceUnary, windowUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived
