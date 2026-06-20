namespace BEDC.Derived.Window6SeamIdentification

def bitAt (word index : Nat) : Nat :=
  (word / (2 ^ (5 - index))) % 2

def weight (word : Nat) : Nat :=
  bitAt word 0 + bitAt word 1 + bitAt word 2 +
    bitAt word 3 + bitAt word 4 + bitAt word 5

def linearAdmissible (word : Nat) : Bool :=
  !((bitAt word 0 == 1) && (bitAt word 1 == 1)) &&
  !((bitAt word 1 == 1) && (bitAt word 2 == 1)) &&
  !((bitAt word 2 == 1) && (bitAt word 3 == 1)) &&
  !((bitAt word 3 == 1) && (bitAt word 4 == 1)) &&
  !((bitAt word 4 == 1) && (bitAt word 5 == 1))

def cyclicNormal (word : Nat) : Bool :=
  linearAdmissible word &&
    !((bitAt word 0 == 1) && (bitAt word 5 == 1))

def endpointCollision (word : Nat) : Bool :=
  linearAdmissible word &&
    (bitAt word 0 == 1) &&
    (bitAt word 5 == 1)

def X6 : List Nat :=
  (List.range 64).filter linearAdmissible

def U1 : List Nat :=
  X6.filter (fun word => cyclicNormal word && (weight word == 1))

def UR : List Nat :=
  X6.filter endpointCollision

def URWeightRows : List (Nat × Nat) :=
  UR.map (fun word => (word, weight word))

def URMinimalDefects : List Nat :=
  UR.filter (fun word => weight word == 2)

def oneBitParents (word : Nat) : List Nat :=
  (List.range 64).filter
    (fun parent =>
      cyclicNormal parent &&
        (weight parent == 1) &&
        (weight word == weight parent + 1) &&
        (List.range 6).all
          (fun index =>
            let pbit := bitAt parent index
            let wbit := bitAt word index
            (pbit == wbit) || ((pbit == 0) && (wbit == 1))))

def minDefectParents : List Nat :=
  oneBitParents 33

def parentsInU1 : Bool :=
  minDefectParents.all (fun parent => U1.contains parent)

def uniqueSeamU1ToUR : Bool :=
  (URMinimalDefects == [33]) &&
    (minDefectParents == [1, 32]) &&
    parentsInU1

def seamGrade : Nat :=
  (8 + 10 - 1) % 10

theorem x6_count_21 :
    X6.length = 21 := by
  decide

theorem u1_cells :
    U1 = [1, 2, 4, 8, 16, 32] := by
  decide

theorem ur_cells :
    UR = [33, 37, 41] := by
  decide

theorem ur_weight_rows :
    URWeightRows = [(33, 2), (37, 3), (41, 3)] := by
  decide

theorem ur_min_defect_100001 :
    URMinimalDefects = [33] := by
  decide

theorem parents_in_u1 :
    minDefectParents = [1, 32] ∧ parentsInU1 = true := by
  decide

theorem unique_seam_u1_to_ur :
    uniqueSeamU1ToUR = true := by
  decide

theorem seam_grade_seven :
    seamGrade = 7 := by
  decide

end BEDC.Derived.Window6SeamIdentification
