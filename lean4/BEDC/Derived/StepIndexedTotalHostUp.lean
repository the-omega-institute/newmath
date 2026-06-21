import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StepIndexedTotalHostUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

structure StepIndexedTotalHostCarrier [AskSetup] [PackageSetup]
    (host fuel trace normal bounded refusal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop where
  host_unary : UnaryHistory host
  fuel_unary : UnaryHistory fuel
  trace_unary : UnaryHistory trace
  normal_unary : UnaryHistory normal
  bounded_unary : UnaryHistory bounded
  refusal_unary : UnaryHistory refusal
  transport_unary : UnaryHistory transport
  route_unary : UnaryHistory route
  provenance_unary : UnaryHistory provenance
  nameCert_unary : UnaryHistory nameCert
  host_fuel_trace : Cont host fuel trace
  trace_bounded_normal : Cont trace bounded normal
  refusal_transport_route : Cont refusal transport route
  provenance_pkg : PkgSig bundle provenance pkg

theorem StepIndexedTotalHostCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameCert ∧
              StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport
                route provenance nameCert bundle pkg)
          (fun row : BHist => hsame row nameCert ∧ Cont host fuel trace)
          (fun row : BHist => hsame row nameCert ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory host ∧
          UnaryHistory fuel ∧
            UnaryHistory trace ∧
              UnaryHistory normal ∧
                UnaryHistory bounded ∧
                  UnaryHistory refusal ∧
                    UnaryHistory transport ∧
                      UnaryHistory route ∧
                        UnaryHistory provenance ∧
                          UnaryHistory nameCert ∧
                            Cont host fuel trace ∧
                              Cont trace bounded normal ∧
                                Cont refusal transport route ∧
                                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory SemanticNameCert hsame
  intro carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameCert ∧
              StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport
                route provenance nameCert bundle pkg)
          (fun row : BHist => hsame row nameCert ∧ Cont host fuel trace)
          (fun row : BHist => hsame row nameCert ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameCert ⟨hsame_refl nameCert, carrier⟩
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
        intro row row' sameRows source
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, source.right.host_fuel_trace⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, source.right.provenance_pkg⟩
  }
  exact
    ⟨cert, carrier.host_unary, carrier.fuel_unary, carrier.trace_unary,
      carrier.normal_unary, carrier.bounded_unary, carrier.refusal_unary,
      carrier.transport_unary, carrier.route_unary, carrier.provenance_unary,
      carrier.nameCert_unary, carrier.host_fuel_trace,
      carrier.trace_bounded_normal, carrier.refusal_transport_route,
      carrier.provenance_pkg⟩

theorem StepIndexedTotalHostCarrier_obligation_surface [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert boundaryRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      Cont normal refusal boundaryRead →
        Cont boundaryRead nameCert namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row host ∨ hsame row fuel ∨ hsame row trace ∨
                    hsame row normal ∨ hsame row bounded ∨ hsame row refusal ∨
                      hsame row boundaryRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont host fuel trace ∧ Cont trace bounded normal ∧
                    Cont normal refusal boundaryRead ∧ Cont boundaryRead nameCert namedRead ∧
                      PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory boundaryRead ∧ UnaryHistory namedRead ∧ Cont host fuel trace ∧
                Cont trace bounded normal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute namedRoute _namedPkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed carrier.normal_unary carrier.refusal_unary boundaryRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed boundaryUnary carrier.nameCert_unary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row host ∨ hsame row fuel ∨ hsame row trace ∨ hsame row normal ∨
              hsame row bounded ∨ hsame row refusal ∨ hsame row boundaryRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont host fuel trace ∧ Cont trace bounded normal ∧
              Cont normal refusal boundaryRead ∧ Cont boundaryRead nameCert namedRead ∧
                PkgSig bundle provenance pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrier.host_fuel_trace, carrier.trace_bounded_normal,
          boundaryRoute, namedRoute, carrier.provenance_pkg⟩
  }
  exact
    ⟨cert, boundaryUnary, namedUnary, carrier.host_fuel_trace,
      carrier.trace_bounded_normal, carrier.provenance_pkg⟩

end BEDC.Derived.StepIndexedTotalHostUp
