# Roadmap

Development roadmap for circle-polygon-overlap.

## Completed

### General Polygon Interior Overlap
- Boundary-walk algorithm for arbitrary convex and non-convex polygons
- Interactive HTML visualization with 2D/3D views
- Exact geometric tests (point-to-segment distance) for numerical stability
- Support for multiple polygon types: square, rectangle, triangle, pentagon,
  hexagon, octagon, custom shapes

### Reference Implementations
- Haskell implementation for numerical experimentation
- Python sanity checks against numerical integration

## In Progress

### Square-Circle Formal Verification (Rocq)
- 8-case geometric decomposition for centered square and circle
- Definitions of geometric primitives (sectors, triangles, segment areas)
- Case analysis and main area formula
- Target: Rocq 8.20+

## Planned

### Multi-Polygon Overlap Calculation
Compute overlap areas for multiple polygons simultaneously.

**Approach:**
- Accept array of polygons as input
- Apply boundary-walk algorithm to each polygon independently
- Return array of individual overlap areas plus total

**UI Changes:**
- Polygon list management panel
- Visual distinction between polygons (different colors)
- Individual and combined area display

### Circle Boundary Mode
Toggle between computing interior area overlap vs perimeter length inside polygon.

**Algorithm:**
- Use same intersection-finding logic
- Sum arc lengths (θ · R) instead of sector areas
- Same complexity, different final calculation

**UI Changes:**
- Mode toggle: "Interior overlap" / "Boundary overlap"
- Highlight boundary segments inside polygons
- Arc length annotations

### Performance Optimizations
For complex polygons with many vertices:
- Spatial indexing for intersection finding
- Bounding box pre-filtering
- Incremental updates for animation

### Extended Formal Verification
Potential future proofs:
- General convex polygon case
- Specific regular polygon cases (triangle, hexagon)
- Boundary mode correctness
