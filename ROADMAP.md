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

### Multi-Polygon Support
- Add/remove polygons with independent colors
- Combined overlap and per-polygon totals displayed in the viewer
- Works with all existing shapes (regular and custom)

### Boundary Mode (Circle Perimeter)
- Toggle between interior area and perimeter overlap
- Arc-length annotations on contributing circle segments
- 3D surface plot normalizes height by circumference in this mode

## In Progress

### Square-Circle Formal Verification (Rocq)
- 8-case geometric decomposition for centered square and circle
- Definitions of geometric primitives (sectors, triangles, segment areas)
- Case analysis and main area formula
- Target: Rocq 8.20+

## Planned

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
