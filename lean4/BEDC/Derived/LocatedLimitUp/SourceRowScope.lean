import BEDC.Derived.LocatedLimitUp.RealSealRoute

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedLimitCarrier_source_row_scope [AskSetup] [PackageSetup]
    {S M T Q E H C P N scheduleRead readbackRead sealRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedLimitCarrier S M T Q E H C P N bundle pkg ->
      Cont S M scheduleRead ->
        Cont scheduleRead T readbackRead ->
          Cont readbackRead Q sealRead ->
            Cont sealRead N sourceRead ->
              PkgSig bundle sourceRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨
                        hsame row E ∨ hsame row sourceRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S M scheduleRead ∧
                        Cont scheduleRead T readbackRead ∧ Cont readbackRead Q sealRead ∧
                          Cont sealRead N sourceRead ∧ PkgSig bundle sourceRead pkg)
                    hsame ∧
                  UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleRoute readbackRoute sealRoute sourceRoute sourcePkg
  obtain ⟨unaryS, unaryM, unaryT, unaryQ, _unaryE, _unaryH, _unaryC, _unaryP,
    unaryN, _provenancePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryS unaryM scheduleRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryT readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryQ sealRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sealUnary unaryN sourceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨ hsame row E ∨
              hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M scheduleRead ∧ Cont scheduleRead T readbackRead ∧
              Cont readbackRead Q sealRead ∧ Cont sealRead N sourceRead ∧
                PkgSig bundle sourceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, readbackRoute, sealRoute, sourceRoute,
          sourcePkg⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, sealUnary, sourceUnary⟩

end BEDC.Derived.LocatedLimitUp
