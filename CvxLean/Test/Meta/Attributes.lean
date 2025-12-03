import CvxLean.Meta.Attributes

/-!
# Attributes Tests

Tests for `/CvxLean/Meta/Attributes.lean` - simp extension attributes for
transformation theorems.
-/

open Lean Meta

-- Test: Verify attribute extensions are registered
#check strongEquivThmExtension
#check equivThmExtension
#check redThmExtension
#check relThmExtension

-- Test: Attributes can be applied to theorems
@[strong_equiv] theorem test_strong_equiv : True := trivial
@[equiv] theorem test_equiv : True := trivial
@[red] theorem test_red : True := trivial
@[rel] theorem test_rel : True := trivial

/-- Test: Verify theorems are retrievable from extensions. -/
def testAttributeRetrieval : MetaM Unit := do
  -- Just verify the extensions exist and are SimpExtensions
  let _ ← strongEquivThmExtension.getTheorems
  let _ ← equivThmExtension.getTheorems
  let _ ← redThmExtension.getTheorems
  let _ ← relThmExtension.getTheorems

#eval testAttributeRetrieval
