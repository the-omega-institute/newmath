import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetacicDecidabilityWitnessCarrier [AskSetup] [PackageSetup]
    (T S B F R H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory F ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
        ∃ packet : MetacicDecidabilityWitnessUp,
          packet = MetacicDecidabilityWitnessUp.mk T S B F R H C P N

theorem MetacicDecidabilityWitnessPublicExport [AskSetup] [PackageSetup]
    {T S B F R H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg →
      Cont T S B →
        Cont B F publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                    hsame row R ∨ hsame row publicRead)
                (fun row : BHist =>
                  hsame row publicRead ∧ Cont T S B ∧ Cont B F publicRead ∧
                    PkgSig bundle publicRead pkg)
                hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier checkerRoute publicRoute publicPkg
  obtain ⟨tUnary, sUnary, _bUnary, fUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have boundedUnary : UnaryHistory B :=
    unary_cont_closed tUnary sUnary checkerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed boundedUnary fUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧
        PkgSig bundle row pkg) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary, publicPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
              hsame row R ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont T S B ∧ Cont B F publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, checkerRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
