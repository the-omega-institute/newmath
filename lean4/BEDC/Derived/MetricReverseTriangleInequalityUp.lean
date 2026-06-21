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

inductive MetricReverseTriangleInequalityUp : Type where
  | mk (M DXZ DYZ G E W R S H C P N : BHist) : MetricReverseTriangleInequalityUp
  deriving DecidableEq

def metricReverseTriangleInequalityFields :
    MetricReverseTriangleInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricReverseTriangleInequalityUp.mk M DXZ DYZ G E W R S H C P N =>
      [M, DXZ, DYZ, G, E, W, R, S, H, C, P, N]

theorem MetricReverseTriangleInequalityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (T : MetricReverseTriangleInequalityUp)
    {M DXZ DYZ G E W R S H C P N distanceGap toleranceRead windowRead regularRead
      realSeal namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    metricReverseTriangleInequalityFields T = [M, DXZ, DYZ, G, E, W, R, S, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory DXZ ->
          UnaryHistory DYZ ->
            UnaryHistory G ->
              UnaryHistory E ->
                UnaryHistory W ->
                  UnaryHistory R ->
                    UnaryHistory S ->
                      UnaryHistory N ->
                        Cont DXZ DYZ distanceGap ->
                          Cont distanceGap G toleranceRead ->
                            Cont toleranceRead E windowRead ->
                              Cont windowRead W regularRead ->
                                Cont regularRead R realSeal ->
                                  Cont realSeal N namedRead ->
                                    PkgSig bundle P pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row M ∨ hsame row DXZ ∨
                                              hsame row DYZ ∨ hsame row G ∨
                                                hsame row E ∨ hsame row W ∨
                                                  hsame row R ∨ hsame row S ∨
                                                    hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont DXZ DYZ distanceGap ∧
                                              Cont distanceGap G toleranceRead ∧
                                                Cont toleranceRead E windowRead ∧
                                                  Cont windowRead W regularRead ∧
                                                    Cont regularRead R realSeal ∧
                                                      Cont realSeal N namedRead ∧
                                                        PkgSig bundle P pkg)
                                          hsame ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: MetricReverseTriangleInequalityUp metricReverseTriangleInequalityFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsDXZ rowsDYZ rowsG rowsE rowsW rowsR rowsS rowsN distanceRoute
    toleranceRoute windowRoute regularRoute sealRoute namedRoute packageRead
  have _acceptedFields :
      metricReverseTriangleInequalityFields T = [M, DXZ, DYZ, G, E, W, R, S, H, C, P, N] :=
    fields
  have distanceUnary : UnaryHistory distanceGap :=
    unary_cont_closed rowsDXZ rowsDYZ distanceRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed distanceUnary rowsG toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary rowsE windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rowsW regularRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularUnary rowsR sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row DXZ ∨ hsame row DYZ ∨ hsame row G ∨
              hsame row E ∨ hsame row W ∨ hsame row R ∨ hsame row S ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont DXZ DYZ distanceGap ∧
              Cont distanceGap G toleranceRead ∧ Cont toleranceRead E windowRead ∧
                Cont windowRead W regularRead ∧ Cont regularRead R realSeal ∧
                  Cont realSeal N namedRead ∧ PkgSig bundle P pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, distanceRoute, toleranceRoute, windowRoute, regularRoute,
          sealRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived
