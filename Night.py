#!/usr/bin/python
#
# ToDo:
#
from datetime import datetime
from itertools import combinations, count, dropwhile, islice, izip, permutations
from math import atan2, cos, hypot, pi, sin, sqrt
from os import _exit
from random import random, randint, seed
from re import split
from sys import argv, maxint
from time import sleep
from traceback import format_exc

#
# Auxiliary library guarded imports
#
try:
    from pygame import init, Surface, SRCALPHA
    from pygame import K_COMMA, K_EQUALS, K_ESCAPE, K_F1, K_F4, K_c, K_d, K_s
    from pygame import K_GREATER, K_LESS, K_MINUS, K_PERIOD, K_PLUS, K_RETURN, K_UNDERSCORE
    from pygame import K_KP_DIVIDE, K_KP_ENTER, K_KP_MINUS, K_KP_MULTIPLY, K_KP_PLUS
    from pygame import KEYDOWN, KMOD_ALT, KMOD_CTRL, KMOD_SHIFT
    from pygame import MOUSEBUTTONDOWN, MOUSEBUTTONUP, MOUSEMOTION
    from pygame import QUIT, VIDEOEXPOSE, VIDEORESIZE
    from pygame import FULLSCREEN, DOUBLEBUF, HWSURFACE, RESIZABLE

    from pygame.display import set_mode, set_caption, flip, Info
    from pygame.draw import aaline, circle
    from pygame.event import get
    from pygame.key import get_mods, set_repeat
except ImportError, ex:
    raise ImportError("%s: %s\n\nPlease install PyGame v1.9.1 or later: http://pygame.org\n" % (ex.__class__.__name__, ex))

try:
    from pygame.font import SysFont
except ImportError, ex:
    SysFont = None
    print "\nWARNING: pygame.font cannot be imported, text information will not be available"

try:
    from shapely.geometry import MultiPoint
except ImportError, ex:
    raise ImportError("%s: %s\n\nPlease install Shapely v1.2.1 or later: http://pypi.python.org/pypi/Shapely\n" % (ex.__class__.__name__, ex))

#
# Constants
#

# Colors
black = (0, 0, 0)
blue = (0, 0, 0xff)
cyan = (0, 0xff, 0xff)
darkgray = (0x80, 0x80, 0x80)
gray = (0xd0, 0xd0, 0xd0)
green = (0, 0xff, 0)
red = (0xff, 0, 0)
white = (0xff, 0xff, 0xff)

# Geometry parameters
inf = float('inf')
CENTER = 'CENTER'
gap = 0.05
rGap = 1 - 2 * gap
lineWidth = 2
pointRadius = 4
fontSize = 15
textlineHeight = 1.5
zoomStep = 0.2
keyDelay = 300
keyInterval = 30
infoPosition = (-fontSize, -int(round(fontSize * 0.75)))
captionPosition = (CENTER, -int(round(fontSize * 0.75)))

CORRECTION = 1.79 # LONG/LAT correction coefficient for N37.9

# Graphic primitives enum
POINTS = 0
LINES = 1
CIRCLES = 2

# Text strings
title = "A Night in the Lonesome October"

usageInfo = """Usage:
python Night.py - start with a single random point
python Night.py <numPoints> - start with the specified number of random points
python Night.py <fileName> - start with points loaded from the specified text or .wpt file"""

keysInfo = """\
                      F1: This help
              Left click: Enable/disable the point
         Ctrl-left click: Add a point
 Alt-left click and drag: Move the point
        Ctrl-right click: Delete the point
     Mouse wheel up/down: Zoom in/out
            Middle click: Reset zoom
                       +: Add a point at random location
                       -: Remove a random point
                       /: Previous algorithm
                       *: Next algorithm
                  S or D: Dump points to a text file named Points#-<date>.txt
                   Enter: Start anew
               Alt-Enter: Toggle fullscreen mode
                  Escape: Exit"""

pointsInfo = """Black points are original movable points, dark gray points are disabled.
Light gray point is trivial centroid of black points.
Gray and blue lines indicate the resolution logic.
Blue points and green lines highlight the solution.
Cyan points are intermediate points occuring in calculation.
Green point is the calculated Center.
The currently employed algorithm and the current number of points are displayed
in the window title and in the bottom right corner of the window, the current
scale is displayed in the bottom left corner."""

helpText = "%s\n\n%s" % (keysInfo, pointsInfo)

infoText = "\n%s - The Great Game Calculation\n\n%s\n\n%s\n\n%s\n" % (title, usageInfo, keysInfo, pointsInfo)

#
# Auxiliary subroutines
#
def grouper(n, iterable):
    return izip(*(iter(iterable),) * n)

def chainToLines(ring):
    prev = None
    for point in ring:
        if prev != None:
            yield (prev, point)
        prev = point

def mean(array):
    return float(sum(array)) / len(array)

def areaCenter(points):
    return tuple(mean(tuple(x)) for x in izip(*points))

def distance((x1, y1), (x2, y2)):
    return hypot(x2 - x1, y2 - y1)

def xdistance(((x1, y1), (x2, y2))):
    return distance((x1, y1), (x2, y2))

def closestPoint(pos, points, avoid = None):
    return min(((point, distance(pos, point)) for point in points), key = lambda (point, distance): distance if point != avoid else maxint)

def xBoxes(((x11, y11), (x12, y12)), ((x21, y21), (x22, y22))):
    (x11, x12) = (min(x11, x12), max(x11, x12))
    (y11, y12) = (min(y11, y12), max(y11, y12))
    (x21, x22) = (min(x21, x22), max(x21, x22))
    (y21, y22) = (min(y21, y22), max(y21, y22))
    if x11 > x22 or x21 > x12 or y11 > y22 or y21 > y12:
        return None
    return (float(max(x11, x21) + min(x12, x22)) / 2, float(max(y11, y21) + min(y12, y22)) / 2)

def xLines(((x11, y11), (x12, y12)), ((x21, y21), (x22, y22)), force = False):
    center = xBoxes(((x11, y11), (x12, y12)), ((x21, y21), (x22, y22)))
    if not center:
        return None
    c = (x22 - x21) * (y11 - y21) - (y22 - y21) * (x11 - x21)
    d = (x12 - x11) * (y11 - y21) - (y12 - y11) * (x11 - x21)
    e = (y22 - y21) * (x12 - x11) - (x22 - x21) * (y12 - y11) # pylint: disable=W0621
    if e: # not parallel
        ce = float(c) / e
        de = float(d) / e
        if 0.0001 <= ce <= 0.9999 and 0.0001 <= de <= 0.9999 and len(set((ce, de, 0, 1))) > 2: # intersect
            return (x11 + ce * (x12 - x11), y11 + ce * (y12 - y11))
        else:
            return None
    elif c and d or not force: # parallel
        return None
    else:
        (((x11, y11), (x12, y12)), ((x21, y21), (x22, y22))) = tuple(sorted((tuple(sorted(((x11, y11), (x12, y12)))), tuple(sorted(((x21, y21), (x22, y22)))))))
        return areaCenter(((x21, y21), min((x22, y22), (x12, y12)))) if x21 <= x12 or y21 <= y12 else None

def triangleCenter((x1, y1), (x2, y2), (x3, y3)):
    return xLines((areaCenter(((x1, y1), (x2, y2))), (x3, y3)), (areaCenter(((x1, y1), (x3, y3))), (x2, y2)), True)

def triangleArea((x1, y1), (x2, y2), (x3, y3)):
    a = distance((x1, y1), (x2, y2))
    b = distance((x1, y1), (x3, y3))
    c = distance((x2, y2), (x3, y3))
    p = float(a + b + c) / 2
    return sqrt(p * (p - a) * (p - b) * (p - c))

def angle(((x1, y1), (x2, y2)), ((x3, y3), (x4, y4))):
    a = atan2(y2 - y1, x2 - x1) - atan2(y4 - y3, x4 - x3)
    return a - 2 * pi if a > pi else a + 2 * pi if a < -pi else a

def positiveAngle(((x1, y1), (x2, y2)), ((x3, y3), (x4, y4)), negative = False):
    diff = angle(((x1, y1), (x2, y2)), ((x3, y3), (x4, y4)))
    return diff if (diff <= 0 if negative else diff >= 0) else (-inf if negative else inf)

def projectPoint((x1, y1), (x2, y2), d):
    a = atan2(y2 - y1, x2 - x1)
    return (x1 + d * cos(a), y1 + d * sin(a))

def renderCenteredText(text, font, color):
    lines = []
    maxWidth = maxLeftWidth = maxRightWidth = maxHeight = 0
    for line in text.splitlines():
        parts = line.split(':')
        if len(parts) == 1:
            render = font.render(line.strip(), True, color)
            (w, h) = render.get_size()
            maxWidth = max(maxWidth, w)
            maxHeight = max(maxHeight, h)
            lines.append((w, h, render))
        else:
            left = font.render(parts[0].strip() + '   ', True, color)
            (lw, lh) = left.get_size()
            maxLeftWidth = max(maxLeftWidth, lw)
            maxHeight = max(maxHeight, lh)
            right = font.render(parts[1].strip(), True, color)
            (rw, rh) = right.get_size()
            maxRightWidth = max(maxRightWidth, rw)
            maxHeight = max(maxHeight, rh)
            lines.append((lw, lh, left, rw, rh, right))
    maxWidth = max(maxWidth, maxLeftWidth + maxRightWidth)
    center = (maxWidth + maxLeftWidth - maxRightWidth) // 2
    hStep = maxHeight * textlineHeight
    extraGap = maxHeight * (textlineHeight - 1)
    surface = Surface((maxWidth, hStep * len(lines) - extraGap), SRCALPHA) # pylint: disable=E1121
    hPos = hStep - extraGap
    for line in lines:
        if len(line) == 3:
            (w, h, render) = line
            surface.blit(render, ((maxWidth - w) // 2, hPos- h))
        else:
            (lw, lh, left, rw, rh, right) = line
            surface.blit(left, (center - lw, hPos - lh))
            surface.blit(right, (center, hPos - rh))
        hPos += hStep
    return surface

#
# Algorithm implementations
#
def calculateThroughDistances(allPoints):
    points = list(allPoints)
    lines = []
    addPoints = []
    while points:
        longest = max(combinations(points, 2), key = xdistance)
        lines.append(longest)
        points.remove(longest[0])
        points.remove(longest[1])
        center = areaCenter(longest)
        if len(points) == 1:
            addPoints = (center,)
            points.append(center)
    return (center,
            (LINES, blue, lines),
            (POINTS, black, allPoints),
            (POINTS, cyan, addPoints))

def calculateThroughBigQuadrilaterals(allPoints):
    points = list(allPoints)
    lines = []
    addPoints = []
    medianLines = []
    while len(points) >= 2:
        newPoints = []
        while len(points) >= 2:
            longest = max(combinations(points, 2), key = xdistance)
            points.remove(longest[0])
            points.remove(longest[1])
            if points:
                ends = tuple(max(((p, l) for p in points), key = xdistance)[0] for l in longest)
                if ends[0] == ends[1]:
                    points.remove(ends[0])
                    ps = longest + (ends[0],)
                    center = areaCenter(ps)
                    lines.extend(combinations(ps, 2))
                else:
                    points.remove(ends[0])
                    points.remove(ends[1])
                    for (a, b, c, d) in ((a, b, c, d) for (a, b, c, d) in permutations(longest + ends) if not xLines((a, b), (c, d)) and not xLines((b, c), (a, d))):
                        break
                    lines.extend(((a, b), (b, c), (c, d), (d, a))) # pylint: disable = W0631
                    medians = ((areaCenter((a, b)), areaCenter((c, d))), (areaCenter((b, c)), areaCenter((d, a)))) # pylint: disable = W0631
                    medianLines.extend(medians)
                    center = xLines(*medians, force = True)
                    assert center
            else:
                lines.append(longest)
                center = areaCenter(longest)
            newPoints.append(center)
        points += newPoints
        addPoints += newPoints
    center = points[0]
    return (center,
            (LINES, cyan, medianLines),
            (LINES, blue, lines),
            (POINTS, black, allPoints),
            (POINTS, cyan, addPoints))

def calculateThroughBiTriangles(allPoints):
    points = list(allPoints)
    centers = None
    lines = []
    longestLines = []
    addPoints = []
    while points:
        if len(points) == 1:
            addPoints = centers
            points += addPoints
        elif len(points) == 2:
            centers = points
            break
        longest = max(combinations(points, 2), key = xdistance)
        longestLines.append(longest)
        ends = tuple(tuple(x[0] for x in sorted(((p, l) for p in points), key = xdistance)[1:3]) for l in longest)
        centers = set(longest + ends[0] + ends[1])
        for point in centers:
            points.remove(point)
        if len(centers) == 3:
            lines.extend(combinations(centers, 2))
        else:
            triangles = tuple((longest[i], ends[i][0], ends[i][1]) for i in (0, 1))
            centers = tuple(triangleCenter(*t) for t in triangles)
            for t in triangles:
                lines.extend(combinations(t, 2))
    center = areaCenter(centers)
    return (center,
            (LINES, black, longestLines),
            (LINES, blue, lines),
            (LINES, green, ((center, c) for c in centers)),
            (POINTS, black, allPoints),
            (POINTS, blue, centers),
            (POINTS, cyan, addPoints))

def calculateThroughAreas(allPoints):
    points = set(allPoints)
    outer = None
    lines = []
    while points:
        if len(points) == 1:
            segments = ()
            center = points.pop()
        elif len(points) == 2:
            segments = (points,)
            center = areaCenter(points)
            points = None
        else:
            convex = MultiPoint(tuple(points)).convex_hull
            exterior = convex.exterior if hasattr(convex, 'exterior') else convex
            coords = set(exterior.coords)
            segments = chainToLines(exterior.coords)
            center = tuple(exterior.centroid.coords)[0]
            points -= coords
        lines.extend(segments)
        if not outer:
            outer = (coords, segments, center)
    lastPoints = (outer[2], center)
    center = areaCenter(lastPoints)
    return (center,
            (LINES, blue, lines),
            (LINES, green, (lastPoints,)),
            (POINTS, black, allPoints),
            (POINTS, blue, lastPoints))

def calculateThroughSegments(allPoints):
    points = list(allPoints)
    closest = min(combinations(points, 2), key = xdistance)
    points.remove(closest[0])
    points.remove(closest[1])
    candidates = tuple(closestPoint(c, points) for c in closest)
    i = int(candidates[0][1] > candidates[1][1])
    point = candidates[i][0]
    firstPoint = closest[1 - i]
    points.remove(point)
    segments = [closest, (closest[i], point)]
    while points:
        (prev, point) = (point, closestPoint(point, points)[0])
        points.remove(point)
        segments.append((prev, point))
    lastPoints = (firstPoint, point)
    center = areaCenter(lastPoints)
    return (center,
            (LINES, blue, segments),
            (LINES, green, (lastPoints,)),
            (POINTS, black, allPoints),
            (POINTS, blue, lastPoints))

def calculateThroughSmallestTriangles(allPoints):
    points = list(allPoints)
    lines = []
    lastLines = []
    center = previousCenter = None
    while len(points) >= 3:
        smallestTriangle = min(combinations(points, 3), key = lambda triangle: max(xdistance(line) for line in combinations(triangle, 2)))
        for point in smallestTriangle:
            points.remove(point)
        lastLines = tuple(combinations(smallestTriangle, 2))
        lines.extend(lastLines)
        previousCenter = center
        center = triangleCenter(*smallestTriangle)
        if len(points) == 2:
            points.append(center)
        elif len(points) == 1:
            if previousCenter:
                points.extend((center, previousCenter))
            else:
                smallestTriangle = (points[0], center)
                lastLines = (smallestTriangle,)
                center = areaCenter(*lastLines)
    return (center,
            (LINES, blue, lines),
            (LINES, green, tuple((center, point) for point in smallestTriangle)),
            (POINTS, black, allPoints),
            (POINTS, blue, smallestTriangle))

def calculateThroughAngles(allPoints):
    points = list(allPoints)
    negative = bool(len(points) % 2 == 0)
    longest = max(combinations(points, 2), key = xdistance)
    points.remove(longest[0])
    points.remove(longest[1])
    lines = []
    prevPoint = startPoint = areaCenter(longest)
    nextPoint = closestPoint(startPoint, points)[0]
    while True:
        points.remove(nextPoint)
        lines.append((prevPoint, nextPoint))
        if not points:
            break
        (prevPoint, nextPoint) = (nextPoint, (max if negative else min)(points, key = lambda point: positiveAngle((prevPoint, nextPoint), (nextPoint, point), negative)))
    center = (2 * nextPoint[0] - prevPoint[0], 2 * nextPoint[1] - prevPoint[1]) # project center point
    return (center,
            (LINES, black, (longest,)),
            (LINES, blue, lines),
            (LINES, green, ((nextPoint, center),)),
            (POINTS, black, allPoints),
            (POINTS, blue, (startPoint,)))

def calculateThroughCircles(allPoints):
    circles = sorted(((point, closestPoint(point, allPoints, point)[1]) for point in allPoints), key = lambda (pos, radius): radius, reverse = True)
    (((x1, y1), r1), ((x2, y2), r2)) = finalCircles = circles[:2]
    finalPoints = ((x1, y1), (x2, y2))
    center = (x1 + (x2 - x1) * r1 / (r1 + r2), y1 + (y2 - y1) * r1 / (r1 + r2))
    return (center,
            (CIRCLES, blue, circles),
            (CIRCLES, green, finalCircles),
            (LINES, green, (finalPoints,)),
            (POINTS, black, allPoints),
            (POINTS, blue, finalPoints))

def calculateThroughDoubleCircles(points):
    innerCircles = sorted(((point, closestPoint(point, points, point)[1] * 0.5) for point in points), key = lambda (point, radius): radius)
    outerCircles = sorted(((pos, min(distance(pos, p) - r for (p, r) in innerCircles if p != pos)) for (pos, radius) in innerCircles), key = lambda (pos, radius): radius, reverse = True)
    (((x1, y1), r1), ((x2, y2), r2)) = finalCircles = outerCircles[:2]
    finalPoints = ((x1, y1), (x2, y2))
    center = (x1 + (x2 - x1) * r1 / (r1 + r2), y1 + (y2 - y1) * r1 / (r1 + r2))
    return (center,
            (CIRCLES, gray, innerCircles),
            (CIRCLES, blue, outerCircles),
            (CIRCLES, green, finalCircles),
            (LINES, green, (finalPoints,)),
            (POINTS, black, points),
            (POINTS, blue, finalPoints))

def calculateThroughInverseMaxDistances(allPoints):
    points = list(allPoints)
    lines = []
    gCenter = areaCenter(points)
    radius = max(distance(p, gCenter) for p in points)
    while points:
        if len(points) == 1:
            last = points[0]
            break
        longest = max(combinations(points, 2), key = xdistance)
        lines.append(longest)
        points.remove(longest[0])
        points.remove(longest[1])
        last = areaCenter(longest)
    center = projectPoint(last, gCenter, radius)
    end = projectPoint(last, gCenter, radius + distance(last, gCenter))
    return (center,
            (LINES, blue, lines),
            (CIRCLES, gray, ((gCenter, radius),)),
            (LINES, gray, ((last, end),)),
            (LINES, green, ((last, center),)),
            (POINTS, black, allPoints),
            (POINTS, gray, (end,)),
            (POINTS, blue, (last,)))

def calculateThroughInverseMinDistances(allPoints):
    points = list(allPoints)
    lines = []
    gCenter = areaCenter(points)
    radius = max(distance(p, gCenter) for p in points)
    while points:
        if len(points) == 1:
            last = points[0]
            break
        longest = min(combinations(points, 2), key = xdistance)
        lines.append(longest)
        points.remove(longest[0])
        points.remove(longest[1])
        last = areaCenter(longest)
    center = projectPoint(last, gCenter, radius)
    end = projectPoint(last, gCenter, radius + distance(last, gCenter))
    return (center,
            (LINES, blue, lines),
            (CIRCLES, gray, ((gCenter, radius),)),
            (LINES, gray, ((last, end),)),
            (LINES, green, ((last, center),)),
            (POINTS, black, allPoints),
            (POINTS, gray, (end,)),
            (POINTS, blue, (last,)))

def calculateThroughPairs(allPoints, rightNumber = 15):
    lines = sorted(combinations(allPoints, 2), key = xdistance)[:rightNumber]
    res = lines[-1]
    return (areaCenter(res),
            (LINES, blue if len(lines) >= rightNumber else red, lines[:-1]),
            (LINES, green, (res,)),
            (POINTS, black, allPoints),
            (POINTS, blue, res))

algorithms = (calculateThroughPairs,
              calculateThroughInverseMinDistances, calculateThroughInverseMaxDistances,
              calculateThroughDoubleCircles, calculateThroughCircles, calculateThroughAngles,
              calculateThroughSmallestTriangles, calculateThroughSegments, calculateThroughAreas,
              calculateThroughBiTriangles, calculateThroughBigQuadrilaterals, calculateThroughDistances)
#
# Main calculation, drawing and interface class
#
class Night: # pylint: disable=R0902
    def __init__(self, args):
        print infoText
        self.numPoints = None
        self.loadedPoints = None
        self.loadedDisabledPoints = None
        self.nAlgorithm = 5
        self.screen = None
        self.drawFunctions = { POINTS: self.drawPoints, LINES: self.drawLines, CIRCLES: self.drawCircles }
        if len(args) == 1:
            self.numPoints = 1
        elif len(args) > 2:
            raise ValueError("ERROR: Too many arguments")
        else:
            arg = args[1].strip()
            try:
                self.numPoints = int(arg)
            except ValueError:
                with open(arg) as f: # Load points from file
                    if arg.lower().endswith('.wpt'): # Ozi waypoints file
                        points = ((float(c[1]), -float(c[0]) * CORRECTION) for c in (line.split(',')[2:4] for line in f.readlines()) if c)
                        disabledPoints = ()
                    else: # Text file with float numbers separated with spaces or commas
                        #points = (grouper(2, (float(i) for i in split('[, ]*', ' '.join(line for line in (line.strip() for line in f.readlines()) if line and line[0] not in '#;')))))
                        points = []
                        disabledPoints = []
                        for coords in (split('[, ]*', line) for line in (line.strip() for line in f.readlines()) if line and line[0] not in '#;'):
                            if len(coords) == 2:
                                points.append(tuple(float(c) for c in coords))
                            elif len(coords) == 3 and coords[2] == 'D':
                                disabledPoints.append(tuple(float(c) for c in coords[:2]))
                            else:
                                raise ValueError("Text file format must be either 'XXX YYY' or 'XXX YYY D'") # pylint: disable=W0511
                self.loadedPoints = tuple(sorted(set(points)))
                self.loadedDisabledPoints = tuple(sorted(set(disabledPoints)))
        seed()
        init()
        set_caption(title)
        set_repeat(keyDelay, keyInterval)
        info = Info()
        self.displaySize = (info.current_w, info.current_h)
        self.windowSize = (min(info.current_w * 2 // 3, info.current_h * 32 // 27), min(info.current_w * 3 // 8, info.current_h * 2 // 3))
        self.font = dropwhile(lambda font: not font, (SysFont(fontName, fontSize, bold = True) for fontName in ('Verdana', 'Arial', None,))).next() if SysFont else None
        self.helpSurface = renderCenteredText(helpText, self.font, black) if self.font else None

    def addRandomPoint(self):
        for point in (tuple(m + random() * s for (m, s) in izip(self.logicalMinPos, self.fullLogicalSize)) for _ in count()):
            if all(distance(p, point) >= 2 * self.logicalPointRadius for p in self.points + self.disabledPoints):
                self.points.append(point)
                return point

    def removeRandomPoint(self):
        if len(self.points) + len(self.disabledPoints) > 1:
            n = randint(0, len(self.points) + len(self.disabledPoints) - 1)
            if n < len(self.points) and len(self.points) > 1:
                return self.points.pop(n)
            return self.disabledPoints.pop(randint(0, len(self.disabledPoints) - 1))
        return None

    def preScaleScreen(self):
        if len(self.points) + len(self.disabledPoints) == 1:
            (self.minPos, self.maxPos, self.logicalSize) = izip(*((x - s // 2 + p, x + s // 2 - p, s - p - p) for (s, p, x) in ((s, s * gap, x) for (s, x) in izip(self.screenSize, self.points[0]))))
        else:
            (self.minPos, self.maxPos) = (tuple(f(point[i] for point in self.points + self.disabledPoints) for i in (0, 1)) for f in (min, max))
            self.logicalSize = tuple(b - a for (a, b) in izip(self.minPos, self.maxPos))

    def scaleScreen(self):
        self.factor = min((rGap * s / l if l else inf) for (s, l) in izip(self.screenSize, self.logicalSize))
        self.offset = tuple(s * 0.5 - (l * 0.5 + m) * self.factor for (s, m, l) in izip(self.screenSize, self.minPos, self.logicalSize))
        self.logicalMinPos = self.screenToLogicalPoint(s * gap for s in self.screenSize)
        self.logicalMaxPos = self.screenToLogicalPoint(s * rGap for s in self.screenSize)
        self.fullLogicalSize = tuple(b - a for (a, b) in izip(self.logicalMinPos, self.logicalMaxPos))
        self.logicalPointRadius = float(pointRadius) / self.factor

    def logicalToScreenPoint(self, pos):
        return tuple(int(round(x * self.factor + offset)) for (x, offset) in izip(pos, self.offset))

    def screenToLogicalPoint(self, pos):
        return tuple(float(x - offset) / self.factor for (x, offset) in izip(pos, self.offset))

    def drawPoints(self, points, color):
        for point in points:
            circle(self.screen, color, self.logicalToScreenPoint(point), pointRadius)

    def drawLine(self, (a, b), color):
        aaline(self.screen, color, a, b, lineWidth)

    def drawLines(self, lines, color):
        for (a, b) in lines:
            self.drawLine((self.logicalToScreenPoint(a), self.logicalToScreenPoint(b)), color)

    def drawCircles(self, circles, color):
        for (pos, radius) in circles:
            circle(self.screen, color, self.logicalToScreenPoint(pos), max(int(round(radius * self.factor)), 1), 1)

    def drawString(self, pos, text, color):
        if not self.font:
            return None
        render = self.font.render(text, True, color)
        size = render.get_size()
        self.screen.blit(render, tuple((s - r) // 2 if p == CENTER else p if p >= 0 else s - r + p for (s, r, p) in izip(self.screenSize, size, pos)))
        return size

    def drawScale(self):
        if not self.font:
            return None
        (x, y) = infoPosition
        x = -x
        dx = int(round(self.screenSize[0] * 0.1))
        dy = int(round(dx * 0.02))
        (_, h) = self.drawString((x + int(round(dx * 0.98)) - self.screenSize[0], y), "%.3g" % (dx / self.factor), black)
        y += self.screenSize[1] - int(round(1.5 * h))
        self.drawLine(((x, y), (x + dx, y)), black)
        self.drawLine(((x, y - dy), (x, y + dy)), black)
        self.drawLine(((x + dx, y - dy), (x + dx, y + dy)), black)

    def setVideoMode(self, fullscreen = False, resolution = None):
        info = Info()
        if not info.wm:
            fullscreen = True
        flags = RESIZABLE
        flags |= FULLSCREEN if fullscreen else 0
        flags |= HWSURFACE | DOUBLEBUF if fullscreen and info.hw else 0
        if resolution:
            self.windowSize = self.screenSize = resolution
        else:
            self.screenSize = self.displaySize if fullscreen else self.windowSize
        self.screen = set_mode(self.screenSize, flags)

    def paint(self):
        if len(self.points) == 1:
            calculation = (self.points[0], (POINTS, green, self.points),)
        elif len(self.points) == 2:
            calculation =  (areaCenter(self.points), (LINES, green, (self.points,)), (POINTS, blue, self.points), (POINTS, green, (areaCenter(self.points),)))
        else:
            calculation = algorithms[self.nAlgorithm](self.points)
        self.center = calculation[0]
        self.screen.fill(white)
        self.drawPoints(self.disabledPoints, darkgray)
        self.drawPoints((areaCenter(self.points),), gray)
        for (kind, color, items) in islice(calculation, 1, None):
            self.drawFunctions[kind](items, color)
        self.drawPoints((self.center,), green)
        self.drawScale()
        tag = '%s/%d' % (algorithms[self.nAlgorithm].func_name[16:], len(self.points))
        set_caption('%s (%s)' % (title, tag))
        textSize = self.drawString(infoPosition, tag, black)
        if self.caption:
            self.drawString(captionPosition, self.caption, black)
        if self.showHelp:
            self.screen.blit(self.helpSurface, tuple((s - 3 * textSize[1] - h) // 2 for (s, h) in izip(self.screenSize, self.helpSurface.get_size())))
        flip()

    def run(self):
        fullscreen = False
        running = True
        self.setVideoMode(fullscreen)
        while running:
            if self.loadedPoints:
                self.points = list(self.loadedPoints)
                self.disabledPoints = list(self.loadedDisabledPoints)
                self.preScaleScreen()
                self.scaleScreen()
            else:
                (self.minPos, self.maxPos, self.logicalSize) = izip(*((p, s - p, s - p - p) for (s, p) in ((s, s * gap) for s in self.screenSize)))
                self.scaleScreen()
                self.points = []
                self.disabledPoints = []
                for _ in xrange(self.numPoints):
                    self.addRandomPoint()
            playing = True
            selected = self.showHelp = self.caption = None
            self.paint()
            while running and playing:
                needPaint = resize = None
                for e in get():
                    if e.type == QUIT:
                        running = False # Alt-F4 or close-click
                    elif e.type == VIDEOEXPOSE:
                        needPaint = True # Just in case
                    elif e.type == VIDEORESIZE:
                        if not fullscreen: # Window resize
                            resize = (fullscreen, e.size)
                    elif e.type == KEYDOWN:
                        if e.key in (K_ESCAPE,):
                            if self.caption: # Escape, hide caption
                                self.caption = None
                                needPaint = True
                            elif self.showHelp: # Hide help
                                self.showHelp = False
                                needPaint = True
                            elif fullscreen: # Exit fullscreen mode
                                fullscreen = False
                                resize = (fullscreen,)
                            else: # Exit application
                                running = False
                        elif e.key in (K_c,) and get_mods() & KMOD_CTRL \
                          or e.key in (K_F4,) and get_mods() & KMOD_ALT:
                            running = False # Ctrl-C or Alt-F4, exit application
                        elif e.key in (K_RETURN, K_KP_ENTER):
                            if get_mods() & KMOD_ALT: # Alt-Enter, toggle fullscreen mode
                                fullscreen = not fullscreen
                                resize = (fullscreen,)
                            elif not selected: # Enter, restart
                                playing = False
                        elif e.key in (K_F1,) and self.helpSurface:
                            self.showHelp = not self.showHelp # F1, show help
                            needPaint = True
                        elif e.key in (K_PLUS, K_EQUALS, K_KP_PLUS) and not selected:
                            self.addRandomPoint() # Plus, add random point
                            needPaint = True
                        elif e.key in (K_MINUS, K_UNDERSCORE, K_KP_MINUS) and not selected:
                            if self.removeRandomPoint(): # Minus, remove random point
                                needPaint = True
                        elif e.key in (K_COMMA, K_LESS, K_KP_DIVIDE): # Switch to previous algorithm
                            self.nAlgorithm = (self.nAlgorithm or len(algorithms)) - 1
                            needPaint = True
                        elif e.key in (K_PERIOD, K_GREATER, K_KP_MULTIPLY): # Switch to next algorithm
                            self.nAlgorithm = self.nAlgorithm + 1 if self.nAlgorithm < len(algorithms) - 1 else 0
                            needPaint = True
                        elif e.key in (K_s, K_d) and not selected: # S or D, dump points to a text file
                            fileName = 'Points%s-%s.txt' % (len(self.points) + len(self.disabledPoints), datetime.now().strftime('%Y%m%d%H%M%S'))
                            with open(fileName, 'w') as f:
                                f.write('#\n# %s resolution\n#\n# Algorithm: %s\n# Points: %d (%d disabled)\n# Center: %f %f (%f)\n#\n' % ((title, algorithms[self.nAlgorithm].func_name[16:], len(self.points) + len(self.disabledPoints), len(self.disabledPoints)) + self.center + (self.center[1] / -CORRECTION,)))
                                f.writelines(('%f %f\n' % point) for point in sorted(self.points))
                                f.writelines(('%f %f D\n' % point) for point in sorted(self.disabledPoints))
                            self.caption = "%s saved" % fileName
                            needPaint = True
                    elif e.type == MOUSEBUTTONDOWN:
                        if e.button == 1 and not selected: # Left click
                            p = self.screenToLogicalPoint(e.pos)
                            (point, dist) = closestPoint(p, self.points + self.disabledPoints)
                            if dist <= self.logicalPointRadius:
                                if get_mods() & KMOD_ALT:
                                    selected = point # Alt-click to existing point, select it
                                elif not get_mods() & (KMOD_SHIFT | KMOD_CTRL): # Simple click to existing point
                                    if point in self.points: # Enabled/disabled a point
                                        if len(self.points) > 1:
                                            self.points.remove(point)
                                            self.disabledPoints.append(point)
                                            needPaint = True
                                    else:
                                        self.disabledPoints.remove(point)
                                        self.points.append(point)
                                        needPaint = True
                            elif get_mods() & KMOD_CTRL and dist >= 2 * self.logicalPointRadius:
                                self.points.append(p) # Ctrl-click to empty space, add new point
                                selected = p
                                needPaint = True
                        elif e.button == 3: # Right click
                            if selected:
                                if selected in self.points:
                                    if len(self.points) > 1: 
                                        self.points.remove(selected) # Right-click on selected enabled point, remove it
                                        selected = None
                                        needPaint = True
                                else:
                                    self.disabledPoints.remove(selected) # Right-click on selected disabled point, remove it
                                    selected = None
                                    needPaint = True
                            elif get_mods() & KMOD_CTRL:
                                (point, dist) = closestPoint(self.screenToLogicalPoint(e.pos), self.points + self.disabledPoints)
                                if dist <= self.logicalPointRadius:
                                    if point in self.points:
                                        if len(self.points) > 1:
                                            self.points.remove(point)  # Ctrl-right-click on existing enabled point, remove it
                                            needPaint = True
                                    else:
                                        self.disabledPoints.remove(point)  # Ctrl-right-click on existing disabled point, remove it
                                        needPaint = True
                        elif e.button == 2: # Middle click, reset zoom
                            self.preScaleScreen()
                            self.scaleScreen()
                            needPaint = True
                        elif e.button in (4, 5): # Wheel zoom
                            diff = tuple(s * zoomStep * (-1 if e.button == 4 else 1) for s in self.logicalSize)
                            self.logicalSize = tuple(s + d for (s, d) in izip(self.logicalSize, diff))
                            self.minPos = tuple(m - d * (p - s * gap) / (s * rGap) for (m, s, p, d) in izip(self.minPos, self.screenSize, e.pos, diff))
                            self.maxPos = tuple(m + d * (1 - (p - s * gap) / (s * rGap)) for (m, s, p, d) in izip(self.maxPos, self.screenSize, e.pos, diff))
                            self.scaleScreen()
                            needPaint = True
                    elif e.type == MOUSEBUTTONUP and e.button == 1: # Release mouse button
                        selected = None # Release point being dragged
                    elif e.type == MOUSEMOTION and selected: # Mouse move
                        p = self.screenToLogicalPoint(e.pos)
                        if closestPoint(p, self.points + self.disabledPoints, selected)[1] >= 2 * self.logicalPointRadius:
                            if selected in self.points:
                                self.points.remove(selected) # Move selected point
                                self.points.append(p)
                            else:
                                self.disabledPoints.remove(selected)
                                self.disabledPoints.append(p)
                            selected = p
                            needPaint = True
                if needPaint or resize:
                    if resize:
                        self.setVideoMode(*resize)
                        self.scaleScreen()
                    self.paint()
                else:
                    sleep(0.01)
#
# main() part
#
def main():
    try:
        Night(argv).run()
    except KeyboardInterrupt:
        pass
    except BaseException:
        print format_exc()
    _exit(0)

if __name__ == '__main__':
    main()
