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

theorem CauchyContinuousMapPacket_continuousmap_boundary [AskSetup] [PackageSetup]
    {W R D E H C P N imageRead sealRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket W R D E H C P N bundle pkg ->
      Cont W D imageRead ->
        Cont imageRead E sealRead ->
          Cont sealRead C boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row boundaryRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W D imageRead ∧
                      Cont imageRead E sealRead ∧ Cont sealRead C boundaryRead ∧
                        PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute boundaryPkg
  obtain ⟨windowsUnary, _regularUnary, toleranceUnary, sealUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, _provenancePkg⟩ := packet
  have imageReadUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary toleranceUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageReadUnary sealUnary sealRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealReadUnary replayUnary boundaryRoute
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D imageRead ∧ Cont imageRead E sealRead ∧
              Cont sealRead C boundaryRead ∧ PkgSig bundle boundaryRead pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, imageRoute, sealRoute, boundaryRoute, boundaryPkg⟩
    }
  exact ⟨cert, imageReadUnary, sealReadUnary, boundaryReadUnary⟩

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

theorem CauchyContinuousMap_continuousmap_boundary
    (M : BEDC.Derived.CauchyContinuousMapUp)
    (windowsUnary : UnaryHistory M.windows)
    (toleranceUnary : UnaryHistory M.toleranceLedger)
    (imageReadbackUnary : UnaryHistory M.imageReadback)
    (sealUnary : UnaryHistory M.realSealHandoff)
    (nameUnary : UnaryHistory M.localName)
    {windowTolerance imageRead sealRead publicRead : BHist} :
    Cont M.windows M.toleranceLedger windowTolerance →
      Cont windowTolerance M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.localName publicRead →
            hsame publicRead
                (append (append (append M.windows
                  (append M.toleranceLedger M.imageReadback)) M.realSealHandoff)
                  M.localName) ∧
              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro windowRoute imageRoute sealRoute publicRoute
  have sealFacts :
      hsame imageRead (append M.windows (append M.toleranceLedger M.imageReadback)) ∧
        hsame sealRead
          (append (append M.windows (append M.toleranceLedger M.imageReadback))
            M.realSealHandoff) :=
    CauchyContinuousMap_real_seal_handoff M windowRoute imageRoute sealRoute
  have publicExact :
      hsame publicRead
        (append (append (append M.windows (append M.toleranceLedger M.imageReadback))
          M.realSealHandoff) M.localName) :=
    publicRoute.trans (congrArg (fun row => append row M.localName) sealFacts.right)
  have windowToleranceUnary : UnaryHistory windowTolerance :=
    unary_cont_closed windowsUnary toleranceUnary windowRoute
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowToleranceUnary imageReadbackUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary nameUnary publicRoute
  exact ⟨publicExact, publicUnary⟩

theorem CauchyContinuousMap_regularity_transport (M : BEDC.Derived.CauchyContinuousMapUp)
    {windowTolerance imageRead transportedImage sealRead : BHist} :
    Cont M.windows M.toleranceLedger windowTolerance →
      Cont windowTolerance M.imageReadback imageRead →
        hsame imageRead transportedImage →
          Cont transportedImage M.realSealHandoff sealRead →
            hsame transportedImage (append M.windows (append M.toleranceLedger M.imageReadback)) ∧
              hsame sealRead
                (append (append M.windows (append M.toleranceLedger M.imageReadback))
                  M.realSealHandoff) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  intro windowRoute imageRoute imageTransport sealRoute
  have imageExact :
      hsame imageRead (append M.windows (append M.toleranceLedger M.imageReadback)) :=
    imageRoute.trans
      ((congrArg (fun row => append row M.imageReadback) windowRoute).trans
        (append_assoc M.windows M.toleranceLedger M.imageReadback))
  have transportedExact :
      hsame transportedImage (append M.windows (append M.toleranceLedger M.imageReadback)) :=
    hsame_trans (hsame_symm imageTransport) imageExact
  constructor
  · exact transportedExact
  · exact sealRoute.trans (congrArg (fun row => append row M.realSealHandoff) transportedExact)

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

theorem CauchyContinuousMap_composition_route [AskSetup] [PackageSetup]
    (M1 M2 : CauchyContinuousMapUp) {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {firstImage firstSeal secondWindow secondImage secondSeal publicRead : BHist} :
    CauchyContinuousMapPacket M1.windows M1.imageReadback M1.toleranceLedger
        M1.realSealHandoff M1.transport M1.replay M1.provenance M1.localName bundle pkg ->
      CauchyContinuousMapPacket M2.windows M2.imageReadback M2.toleranceLedger
          M2.realSealHandoff M2.transport M2.replay M2.provenance M2.localName bundle pkg ->
        Cont M1.windows M1.imageReadback firstImage ->
          Cont firstImage M1.realSealHandoff firstSeal ->
            Cont firstSeal M2.windows secondWindow ->
              Cont secondWindow M2.imageReadback secondImage ->
                Cont secondImage M2.realSealHandoff secondSeal ->
                  Cont secondSeal M2.localName publicRead ->
                    PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M1.windows ∨ hsame row M1.imageReadback ∨
                              hsame row M1.realSealHandoff ∨ hsame row M2.windows ∨
                                hsame row M2.imageReadback ∨ hsame row M2.realSealHandoff ∨
                                  hsame row publicRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet1 packet2 firstImageRoute firstSealRoute secondWindowRoute secondImageRoute
    secondSealRoute publicRoute publicPkg
  obtain ⟨firstWindowsUnary, firstImageReadbackUnary, _firstToleranceUnary,
    firstSealUnary, _firstTransportUnary, _firstReplayUnary, _firstProvenanceUnary,
    _firstLocalUnary, _firstProvenancePkg⟩ := packet1
  obtain ⟨secondWindowsUnary, secondImageReadbackUnary, _secondToleranceUnary,
    secondSealUnary, _secondTransportUnary, _secondReplayUnary, _secondProvenanceUnary,
    secondLocalUnary, _secondProvenancePkg⟩ := packet2
  have firstImageUnary : UnaryHistory firstImage :=
    unary_cont_closed firstWindowsUnary firstImageReadbackUnary firstImageRoute
  have firstSealReadUnary : UnaryHistory firstSeal :=
    unary_cont_closed firstImageUnary firstSealUnary firstSealRoute
  have secondWindowUnary : UnaryHistory secondWindow :=
    unary_cont_closed firstSealReadUnary secondWindowsUnary secondWindowRoute
  have secondImageUnary : UnaryHistory secondImage :=
    unary_cont_closed secondWindowUnary secondImageReadbackUnary secondImageRoute
  have secondSealReadUnary : UnaryHistory secondSeal :=
    unary_cont_closed secondImageUnary secondSealUnary secondSealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed secondSealReadUnary secondLocalUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M1.windows ∨ hsame row M1.imageReadback ∨
              hsame row M1.realSealHandoff ∨ hsame row M2.windows ∨
                hsame row M2.imageReadback ∨ hsame row M2.realSealHandoff ∨
                  hsame row publicRead)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem CauchyContinuousMap_modulus_boundary_nonescape [AskSetup] [PackageSetup]
    (M : BEDC.Derived.CauchyContinuousMapUp) {modulusRead imageRead sealRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay boundaryRead →
            Cont boundaryRead M.localName modulusRead →
              hsame modulusRead
                  (append (append (append (append M.windows M.imageReadback)
                    M.realSealHandoff) M.replay) M.localName) ∧
                UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute modulusRoute
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, sealUnary,
    _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    _provenancePkg⟩ := packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealReadUnary replayUnary boundaryRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundaryReadUnary localNameUnary modulusRoute
  have sealExact :
      hsame sealRead (append (append M.windows M.imageReadback) M.realSealHandoff) :=
    sealRoute.trans (congrArg (fun row => append row M.realSealHandoff) imageRoute)
  have boundaryExact :
      hsame boundaryRead
        (append (append (append M.windows M.imageReadback) M.realSealHandoff) M.replay) :=
    boundaryRoute.trans (congrArg (fun row => append row M.replay) sealExact)
  have modulusExact :
      hsame modulusRead
        (append (append (append (append M.windows M.imageReadback)
          M.realSealHandoff) M.replay) M.localName) :=
    modulusRoute.trans (congrArg (fun row => append row M.localName) boundaryExact)
  exact ⟨modulusExact, modulusUnary⟩

end CauchyContinuousMapUp

end BEDC.Derived
