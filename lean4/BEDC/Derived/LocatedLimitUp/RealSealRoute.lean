import BEDC.Derived.LocatedLimitUp.TasteGate
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

def LocatedLimitCarrier [AskSetup] [PackageSetup]
    (sequence modulus schedule readback sealRow transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig UnaryHistory
  UnaryHistory sequence ∧ UnaryHistory modulus ∧ UnaryHistory schedule ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        PkgSig bundle provenance pkg

theorem LocatedLimit_real_seal_route [AskSetup] [PackageSetup]
    {S M T Q E H C P N scheduleRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S M scheduleRead ->
      Cont scheduleRead T readbackRead ->
        Cont readbackRead Q sealRead ->
          PkgSig bundle P pkg ->
            UnaryHistory S ->
              UnaryHistory M ->
                UnaryHistory T ->
                  UnaryHistory Q ->
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨
                            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row scheduleRead ∨
                                hsame row readbackRead ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S M scheduleRead ∧
                            Cont scheduleRead T readbackRead ∧
                              Cont readbackRead Q sealRead ∧ PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro scheduleCont readbackCont sealCont pkgP unaryS unaryM unaryT unaryQ
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryS unaryM scheduleCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryT readbackCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryQ sealCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row scheduleRead ∨ hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M scheduleRead ∧ Cont scheduleRead T readbackRead ∧
              Cont readbackRead Q sealRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleCont, readbackCont, sealCont, pkgP⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, sealUnary⟩

theorem LocatedLimitRealSealNonescape [AskSetup] [PackageSetup]
    {sequence modulus schedule readback sealRow transport replay provenance name scheduleRead
      regularRead sealedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedLimitCarrier sequence modulus schedule readback sealRow transport replay provenance
        name bundle pkg →
      Cont sequence modulus scheduleRead →
        Cont scheduleRead readback regularRead →
          Cont regularRead sealRow sealedRead →
            Cont sealedRead name namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sequence ∨ hsame row modulus ∨ hsame row schedule ∨
                        hsame row readback ∨ hsame row sealRow ∨ hsame row sealedRead ∨
                          hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory sealedRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleRoute regularRoute sealedRoute namedRoute namedPkg
  obtain ⟨sequenceUnary, modulusUnary, _scheduleUnary, readbackUnary, sealRowUnary,
    _transportUnary, _replayUnary, _provenanceUnary, nameUnary, provenancePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed sequenceUnary modulusUnary scheduleRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleUnary readbackUnary regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary sealRowUnary sealedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealedUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row modulus ∨ hsame row schedule ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row sealedRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, sealedUnary, namedUnary⟩

end BEDC.Derived.LocatedLimitUp
