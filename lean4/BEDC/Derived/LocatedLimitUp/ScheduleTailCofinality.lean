import BEDC.Derived.LocatedLimitUp.RealSealRoute
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedLimitCarrier_schedule_tail_cofinality [AskSetup] [PackageSetup]
    {S M T Q E H C P N scheduleRead readbackRead sealRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedLimitCarrier S M T Q E H C P N bundle pkg ->
      Cont S M scheduleRead ->
        Cont scheduleRead T readbackRead ->
          Cont readbackRead Q sealRead ->
            Cont sealRead E tailRead ->
              PkgSig bundle P pkg ->
                UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory tailRead ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨
                          hsame row E ∨ hsame row tailRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S M scheduleRead ∧
                          Cont scheduleRead T readbackRead ∧ Cont readbackRead Q sealRead ∧
                            Cont sealRead E tailRead ∧ PkgSig bundle P pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleCont readbackCont sealCont tailCont pkgP
  obtain ⟨unaryS, unaryM, unaryT, unaryQ, unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _pkgProvenance⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryS unaryM scheduleCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryT readbackCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryQ sealCont
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sealUnary unaryE tailCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨ hsame row E ∨
            hsame row tailRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S M scheduleRead ∧ Cont scheduleRead T readbackRead ∧
            Cont readbackRead Q sealRead ∧ Cont sealRead E tailRead ∧
              PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleCont, readbackCont, sealCont, tailCont, pkgP⟩
  }
  exact ⟨scheduleUnary, readbackUnary, sealUnary, tailUnary, cert⟩

end BEDC.Derived.LocatedLimitUp
