# Migration Plan: Repository Scope Expansion and Renaming

## Project Evolution

### Historical Scope
- **Original (inception):** Circle interior ∩ Square interior overlap analysis
- **Current (implemented):** Circle interior ∩ Arbitrary polygon interior overlap
- **Future (planned):**
  1. Circle interior ∩ Multiple polygon interiors (union/combined regions)
  2. Circle boundary ∩ Polygon interiors (perimeter-based overlap calculation)

### Proposed Repository Name
**`circle-polygon-overlap`**

**Rationale:**
- Captures the core geometric relationship (circle ↔ polygon)
- General enough to accommodate multiple polygons
- Works for both interior and boundary overlap modes
- Shorter and clearer than the current `proofs-square-circle-overlap`
- Maintains the "overlap" focus which is the central computational task

**Alternative names considered:**
- `verified-geometric-overlap` - too broad, loses the circle-polygon focus
- `polygon-region-overlap` - doesn't emphasize the circle component
- `circle-region-geometry` - less clear about the overlap computation

---

## Migration Phases

### Phase 1: Update Documentation to Reflect Current and Future Scope

#### 1.1 Update `README.md`
- [ ] Change project title from "proofs-square-circle-overlap" to "circle-polygon-overlap"
- [ ] Update project description to emphasize general polygon support as primary feature
- [ ] Reframe square-circle as a special case, not the main focus
- [ ] Add new "Roadmap" or "Future Enhancements" section with:
  - Multiple polygon support
  - Circle boundary mode (perimeter overlap)
- [ ] Update repository layout section with new filenames
- [ ] Clarify that square-specific formal verification is one component, general algorithm is another

#### 1.2 Update `Spec.txt`
- [ ] Add header noting the specification covers the general polygon algorithm
- [ ] Add section describing planned enhancements:
  - Multi-region overlap (union of polygon interiors)
  - Boundary mode (circle perimeter vs polygon interiors)
- [ ] Document algorithmic considerations for these extensions

#### 1.3 Create or Update `ROADMAP.md`
- [ ] Create a dedicated roadmap file documenting:
  - **Completed:** General polygon interior overlap
  - **In Progress:** Square-circle formal verification in Rocq
  - **Planned:**
    - Multi-polygon overlap calculation
    - Circle boundary mode toggle
    - Performance optimizations for complex polygons
    - Additional formal verification for general polygon cases

#### 1.4 Update `IDEA.txt`
- [ ] Expand to acknowledge the generalized boundary-walk algorithm
- [ ] Note the relationship between the original square-circle question and the general solution

---

### Phase 2: Rename Files to Reflect Broader Scope

#### 2.1 HTML Viewer
- [ ] Rename `circle-square-overlap.html` → `circle-polygon-overlap.html`
- [ ] Update any internal comments or metadata in the HTML file
- [ ] Update README.md references to the new filename

#### 2.2 Haskell Reference Implementation
- [ ] Rename `Haskell/Area of overlap between circle and square.hs` → `Haskell/CirclePolygonOverlap.hs`
- [ ] Consider whether to keep the old file for the specific square-circle case analysis
- [ ] Update README.md references

#### 2.3 Visual Assets (Optional)
- [ ] Decide whether to rename `Rough/Area of overlap between circle and square - 2D (Tidy Working).png`
  - **Recommendation:** Keep the current name since it specifically documents the 8-case square analysis
  - This is a historical artifact illustrating a specific case, not a general diagram

---

### Phase 3: Update Code References and Namespaces

**Note:** This phase requires careful consideration of the formal verification work in progress.

#### 3.1 Rocq Module Namespace (OPTIONAL - Consider Carefully)

**Option A: Keep `SquareCircleOverlap` namespace**
- **Pros:**
  - No disruption to ongoing formal verification work
  - Accurately describes the specific theorem being proven
  - Formal proofs focus on the square case, not general polygons
- **Cons:**
  - Namespace doesn't match repository name
  - May be confusing for newcomers

**Option B: Rename to `CirclePolygonOverlap` or `GeometricOverlap`**
- **Pros:**
  - Consistency across repository
  - Better alignment with general scope
- **Cons:**
  - Requires updating `Rocq/_CoqProject`
  - Requires renaming `Rocq/SquareCircleOverlap.v`
  - May disrupt work-in-progress proofs
  - More complex migration

**Recommendation:** **Keep `SquareCircleOverlap` namespace** for now. The formal verification specifically addresses the square-circle case with 8-case decomposition. If/when general polygon formal verification is added, create a separate module `CirclePolygonOverlap.v` alongside the existing one.

#### 3.2 If Choosing Option B (Rename Rocq Namespace):
- [ ] Rename `Rocq/SquareCircleOverlap.v` → `Rocq/CirclePolygonOverlap.v`
- [ ] Update `Rocq/_CoqProject`: change `-Q . SquareCircleOverlap` → `-Q . CirclePolygonOverlap`
- [ ] Regenerate Makefile: `cd Rocq && coq_makefile -f _CoqProject -o Makefile`
- [ ] Update any `Require` statements in .v files
- [ ] Update README.md references to the module name

---

### Phase 4: Rename Git Repository

#### 4.1 Local Repository Update
```bash
# The directory name doesn't need to match the remote repo name,
# but for consistency you may want to rename it:
cd "/mnt/e/My Creative/Nux-Git/Public Repos/"
mv proofs-square-circle-overlap circle-polygon-overlap
cd circle-polygon-overlap
```

#### 4.2 GitHub Repository Rename
**Manual steps on GitHub:**
1. Go to repository settings on GitHub
2. Navigate to "Repository name" field
3. Change from `proofs-square-circle-overlap` to `circle-polygon-overlap`
4. GitHub will automatically set up redirects from the old URL

**Git remote update (if needed):**
```bash
# Check current remote
git remote -v

# If it shows the old URL, update it:
git remote set-url origin https://github.com/YOUR_USERNAME/circle-polygon-overlap.git

# Or for SSH:
git remote set-url origin git@github.com:YOUR_USERNAME/circle-polygon-overlap.git
```

**Note:** GitHub automatically redirects from old repository URLs, so existing clones will continue to work even if you don't update the remote URL.

#### 4.3 Update Any External References
- [ ] Update links in any external documentation
- [ ] Update links in blog posts or articles
- [ ] Update links in issue trackers or project boards

---

### Phase 5: Verify Everything Still Works

#### 5.1 Build System Verification
```bash
# Test Rocq proofs still compile
cd Rocq
make clean
make

# Expected: Successful compilation with no errors
```

#### 5.2 HTML Viewer Testing
- [ ] Open `circle-polygon-overlap.html` in browser
- [ ] Test all polygon shapes (square, triangle, pentagon, hexagon, octagon, custom)
- [ ] Verify 3D surface plot renders correctly
- [ ] Test animation feature
- [ ] Verify overlap calculations are accurate

#### 5.3 Git Verification
```bash
# Verify git status is clean
git status

# Verify remote is correct
git remote -v

# Test pushing a small change
git add .
git commit -m "Complete repository migration and renaming"
git push
```

---

## Post-Migration: Implementing Future Features

### Feature 1: Multiple Polygon Support

**Design considerations:**
- **Input format:** Array of polygons `[polygon1, polygon2, ...]`
- **Union vs. separate:**
  - Option A: Compute overlap with union of all polygon interiors
  - Option B: Compute separate overlap for each polygon, return array of areas
  - **Recommendation:** Start with Option B (simpler, more flexible)
- **UI changes:**
  - Add polygon list panel
  - Allow adding/removing polygons
  - Visual distinction between polygons (different colors)
- **Algorithm:** Apply existing boundary-walk algorithm to each polygon independently

**Implementation checklist:**
- [ ] Extend data structure to hold multiple polygons
- [ ] Update UI to manage polygon list
- [ ] Modify rendering to display multiple polygons
- [ ] Compute overlap for each polygon separately
- [ ] Display total combined overlap and individual areas
- [ ] Update documentation

### Feature 2: Circle Boundary Mode

**Design considerations:**
- **Metric:** Total length of circle perimeter inside all polygon interiors
- **Toggle UI:** Checkbox or radio buttons: "Interior overlap" vs "Boundary overlap"
- **Algorithm changes:**
  - Find circle-polygon intersections (same as current)
  - For each arc segment between intersections, check if arc is inside polygon
  - Sum the arc lengths (not sector areas)
- **Visualization:**
  - Highlight boundary segments inside polygons differently
  - Show arc length annotations

**Implementation checklist:**
- [ ] Add mode toggle to UI
- [ ] Implement arc length calculation (θ · R for arc angle θ)
- [ ] Modify overlap calculation to compute perimeter instead of area
- [ ] Update visualization to show boundary-only mode
- [ ] Add unit selector (for length vs area)
- [ ] Update documentation and examples

---

## Summary Checklist

### Documentation Updates
- [ ] Update README.md with new project name and scope
- [ ] Update Spec.txt with future plans
- [ ] Create ROADMAP.md
- [ ] Update IDEA.txt

### File Renaming
- [ ] Rename `circle-square-overlap.html` to `circle-polygon-overlap.html`
- [ ] Optionally rename Haskell file
- [ ] Update all documentation references

### Namespace Updates
- [ ] Decide on Rocq namespace strategy
- [ ] If renaming: update .v files and _CoqProject
- [ ] If keeping: document the decision

### Repository Renaming
- [ ] Rename local directory
- [ ] Rename GitHub repository
- [ ] Update git remote URL
- [ ] Update external references

### Verification
- [ ] Build Rocq proofs
- [ ] Test HTML viewer
- [ ] Verify git workflow
- [ ] Commit and push changes

### Future Implementation
- [ ] Plan multi-polygon feature architecture
- [ ] Plan boundary mode feature architecture
- [ ] Prioritize implementation order
