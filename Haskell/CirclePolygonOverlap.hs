#!/usr/bin/env stack
-- stack --resolver nightly-2022-07-04 ghci --package extra-1.7.12 --package containers-0.6.5.1

-- Can we solve this problem more effectively with fourier series?
-- By this I mean, can we consider a circle and a square as being 2D indicator functions similar to the 1D Heaviside function and similarly approximate them with "sine waves", take their product and integrate over them to find the area of overlap?

arcAngle radius sagitta = 2 * acos((radius - sagitta)/radius)
circleArea radius
    = let r = radius
      in pi*r^2
segmentArea radius sagitta
    = let r = radius
          s = sagitta
      in r^2 * acos (1-s/r) - (r-s)*(sqrt (r^2 - (r-s)^2))
sectorArea radius sagitta
    = let r = radius
          s = sagitta
          theta = arcAngle r s
      in sectorArea' r theta
sectorArea' radius theta
    = let r = radius
      in theta * r^2 / 2
sectorMinusSegmentTriangleArea radius sagitta
    = let r = radius
          s = sagitta
      in (r-s)*(sqrt (r^2 - (r-s)^2))

caseAOverlapArea radius = circleArea radius
caseBOverlapArea radius circleCentreFromCorner@(x,y)
    = let r = radius
      in circleArea r - segmentArea r y
caseCOverlapArea radius circleCentreFromCorner@(x,y)
    = let r = radius
      in circleArea r - segmentArea r x - segmentArea r y
caseDOverlapArea radius circleCentreFromCorner@(x,y)
    = let r = radius
      in x*y + (1/2) * x * (sqrt $ r^2 - x^2)
             + (1/2) * x * (sqrt $ r^2 - y^2)
             + r^2 * asin (sqrt ((x + sqrt (r^2 - y^2))^2 + (y + sqrt (r^2 - x^2))^2) / (2 * r))
caseEOverlapArea radius circleCentreFromCorner@(x,y)
    = let r = radius
      in segmentArea r y
caseFOverlapArea radius circleCentreFromCorner@(x,y)
    = let r = radius
      in circleArea r - caseDOverlapArea radius (x,-y) - segmentArea r x
caseGOverlapArea radius circleCentreFromCorner@(x,y)
    = let r = radius
          x' = (sqrt $ r^2 - y^2) + x
          y' = (sqrt $ r^2 - x^2) + y
          theta1 = atan2 (-y) (sqrt $ r^2 - y^2)
          theta2 = atan2 (sqrt $ r^2 - x^2) (-x)
          theta = theta2 - theta1
      in sectorArea' r theta - x'*(-y)/2 - y'*(-x)/2
caseHOverlapArea radius circleCentreFromCorner@(x,y) = 0
