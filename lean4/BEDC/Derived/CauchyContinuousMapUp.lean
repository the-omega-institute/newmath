import BEDC.FKernel.Ask
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

structure CauchyContinuousMapUp where
  windows : BHist
  imageReadback : BHist
  toleranceLedger : BHist
  realSealHandoff : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist
deriving DecidableEq

namespace CauchyContinuousMapUp

def CauchyContinuousMapPacket [AskSetup] [PackageSetup]
    (W R D E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg

theorem CauchyContinuousMapPacket_namecert_obligations [AskSetup] [PackageSetup]
    {W R D E H C P N imageRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket W R D E H C P N bundle pkg →
      Cont W D imageRead →
        Cont imageRead E sealRead →
          Cont sealRead N publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                      hsame row imageRead ∨ hsame row sealRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    hsame row publicRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig SemanticNameCert
  intro packet imageRoute sealRoute publicRoute publicPkg
  obtain ⟨windowsUnary, _regularUnary, toleranceUnary, sealUnary, _transportUnary,
    _replayUnary, provenanceUnary, localNameUnary, provenancePkg⟩ := packet
  have imageReadUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary toleranceUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageReadUnary sealUnary sealRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
            hsame row imageRead ∨ hsame row sealRead ∨ hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro (hsame_refl publicRead) publicReadUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        have samePublic : hsame row' publicRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have rowUnary : UnaryHistory row' :=
          unary_transport source.right sameRows
        exact And.intro samePublic rowUnary
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro row source
      exact And.intro source.left (And.intro provenancePkg publicPkg)
  }
  exact ⟨cert, imageReadUnary, sealReadUnary, publicReadUnary⟩

theorem CauchyContinuousMap_regseqrat_image (M : BEDC.Derived.CauchyContinuousMapUp)
    {windowTolerance imageRead : BHist} :
    Cont M.windows M.toleranceLedger windowTolerance ->
      Cont windowTolerance M.imageReadback imageRead ->
        hsame imageRead (append M.windows (append M.toleranceLedger M.imageReadback)) ∧
          hsame M.imageReadback M.imageReadback := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  intro windowRoute imageRoute
  constructor
  · exact imageRoute.trans (congrArg (fun row => append row M.imageReadback) windowRoute)
      |>.trans (append_assoc M.windows M.toleranceLedger M.imageReadback)
  · exact hsame_refl M.imageReadback

theorem CauchyContinuousMap_real_seal_handoff (M : BEDC.Derived.CauchyContinuousMapUp)
    {windowTolerance imageRead sealRead : BHist} :
    Cont M.windows M.toleranceLedger windowTolerance →
      Cont windowTolerance M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          hsame imageRead (append M.windows (append M.toleranceLedger M.imageReadback)) ∧
            hsame sealRead
              (append (append M.windows (append M.toleranceLedger M.imageReadback))
                M.realSealHandoff) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  intro windowRoute imageRoute sealRoute
  have imageExact :
      hsame imageRead (append M.windows (append M.toleranceLedger M.imageReadback)) :=
    imageRoute.trans
      ((congrArg (fun row => append row M.imageReadback) windowRoute).trans
        (append_assoc M.windows M.toleranceLedger M.imageReadback))
  constructor
  · exact imageExact
  · exact sealRoute.trans (congrArg (fun row => append row M.realSealHandoff) imageExact)

theorem CauchyContinuousMap_window_composition
    (M1 M2 : BEDC.Derived.CauchyContinuousMapUp)
    {firstImage firstSeal secondWindow secondImage secondSeal : BHist} :
    Cont M1.windows M1.imageReadback firstImage →
      Cont firstImage M1.realSealHandoff firstSeal →
        Cont firstSeal M2.windows secondWindow →
          Cont secondWindow M2.imageReadback secondImage →
            Cont secondImage M2.realSealHandoff secondSeal →
              hsame secondSeal
                (append (append (append (append M1.windows M1.imageReadback)
                  M1.realSealHandoff) M2.windows)
                  (append M2.imageReadback M2.realSealHandoff)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  intro firstImageRoute firstSealRoute secondWindowRoute secondImageRoute secondSealRoute
  cases firstImageRoute
  cases firstSealRoute
  cases secondWindowRoute
  cases secondImageRoute
  cases secondSealRoute
  exact append_assoc
    (append (append (append M1.windows M1.imageReadback) M1.realSealHandoff) M2.windows)
    M2.imageReadback
    M2.realSealHandoff

end CauchyContinuousMapUp

end BEDC.Derived
