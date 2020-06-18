#!/usr/bin/env python

# eggbot_hatch.py
#
# Generate hatch fills for the closed paths (polygons) in the currently
# selected document elements.  If no elements are selected, then all the
# polygons throughout the document are hatched.  The fill rule is an odd/even
# rule: odd numbered intersections (1, 3, 5, etc.) are a hatch line entering
# a polygon while even numbered intersections (2, 4, 6, etc.) are the same
# hatch line exiting the polygon.
#
# This extension first decomposes the selected <path>, <rect>, <line>,
# <polyline>, <polygon>, <circle>, and <ellipse> elements into individual
# moveto and lineto coordinates using the same procedure that eggbot.py uses
# for plotting.  These coordinates are then used to build vertex lists.
# Only the vertex lists corresponding to polygons (closed paths) are
# kept.  Note that a single graphical element may be composed of several
# subpaths, each subpath potentially a polygon.
#
# Once the lists of all the vertices are built, potential hatch lines are
# "projected" through the bounding box containing all of the vertices.
# For each potential hatch line, all intersections with all the polygon
# edges are determined.  These intersections are stored as decimal fractions
# indicating where along the length of the hatch line the intersection
# occurs.  These values will always be in the range [0, 1].  A value of 0
# indicates that the intersection is at the start of the hatch line, a value
# of 0.5 midway, and a value of 1 at the end of the hatch line.
#
# For a given hatch line, all the fractional values are sorted and any
# duplicates removed.  Duplicates occur, for instance, when the hatch
# line passes through a polygon vertex and thus intersects two edges
# segments of the polygon: the end of one edge and the start of
# another.
#
# Once sorted and duplicates removed, an odd/even rule is applied to
# determine which segments of the potential hatch line are within
# polygons.  These segments found to be within polygons are then saved
# and become the hatch fill lines which will be drawn.
#
# With each saved hatch fill line, information about which SVG graphical
# element it is within is saved.  This way, the hatch fill lines can
# later be grouped with the element they are associated with.  This makes
# it possible to manipulate the two -- graphical element and hatch lines --
# as a single object within Inkscape.
#
# Note: we also save the transformation matrix for each graphical element.
# That way, when we group the hatch fills with the element they are
# filling, we can invert the transformation.  That is, in order to compute
# the hatch fills, we first have had apply ALL applicable transforms to
# all the graphical elements.  We need to do that so that we know where in
# the drawing  each of the graphical elements are relative to one another.
# However, this means that the hatch lines have been computed in a setting
# where no further transforms are needed.  If we then put these hatch lines
# into the same groups as the elements being hatched in the ORIGINAL
# drawing, then the hatch lines will have transforms applied again.  So,
# once we compute the hatch lines, we need to invert the transforms of
# the group they will be placed in and apply this inverse transform to the
# hatch lines.  Hence the need to save the transform matrix for every
# graphical element.

# Written by Daniel C. Newman for the Eggbot Project
# dan dot newman at mtbaldy dot us
# Last updated 28 November 2010
# 15 October 2010

# Updated by Windell H. Oskay, 6/14/2012
# Added tolerance parameter

# Update by Daniel C. Newman, 6/20/2012
# Add min span/gap width

# Updated by Windell H. Oskay, 1/8/2016
# Added live preview and correct issue with nonzero min gap
# https://github.com/evil-mad/EggBot/issues/32

# Updated by Sheldon B. Michaels, 1/11/2016
# shel at shel dot net
# Added feature: Option to join hatch segments that are "nearby", to minimize pen lifts
# The joins are made using cubic Bezier segments.
# https://github.com/evil-mad/EggBot/issues/36
# Known issues:
#	1. Sometimes leaps across narrow gaps
#		Status: work in progress
#	2. Curves extend beyond boundary
#		Status: work in progress

# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
import string
import sys
from tkinter import *
from tkinter import filedialog
from tkinter.filedialog import asksaveasfile
from tkinter import messagebox
import sys

import svg_view
from ink_extensions import inkex, simpletransform, simplepath, cubicsuperpath, bezmisc, simplestyle
sys.path.insert(0, './ink_extensions') # (Import from lib folder)
from ink_extensions.simpletransform import *
import math
from svg_view import *

root = Tk()
root.geometry("450x420")  # Width x Height
root.title("egg_bot_gui")
# ***main menue***
menu = Menu(root)
root.config(menu=menu)

N_PAGE_WIDTH = 3200
N_PAGE_HEIGHT = 800
def set_size():
    canvas_w = (Entry_box_6.get())
    canvas_h = (Entry_box_7.get())
    N_PAGE_WIDTH = canvas_w
    N_PAGE_HEIGHT = canvas_h


F_DEGREE_ANGLE_DISCREPANCY_BELOW_WHICH_TWO_LINES_ARE_PRESUMED_COLINEAR = 1.0  # ''' Just a guess as to what might be useful
F_RADIAN_ANGLE_DISCREPANCY_BELOW_WHICH_TWO_LINES_ARE_PRESUMED_COLINEAR = math.radians(
    F_DEGREE_ANGLE_DISCREPANCY_BELOW_WHICH_TWO_LINES_ARE_PRESUMED_COLINEAR)
F_MAXIMUM_BEZIER_CONTROL_POINT_DISTANCE = 5.0  # ''' Just trying it out
F_MINGAP_SMALL_VALUE = 0.0000001  # Was 0.00001 in the original version which did not have joined lines.
# Reducing this by a factor of 100 decreased probability of occurrence of
# the bug in the original, which got confused when the path barely
# grazed a corner.

'''
Geometry 101: Determing if two lines intersect

A line L is defined by two points in space P1 and P2.  Any point P on the
line L satisfies

	P = P1 + s (P2 - P1)

for some value of the real number s in the range (-infinity, infinity).
If we confine s to the range [0, 1] then we've described the line segment
with end points P1 and P2.

Consider now the line La defined by the points P1 and P2, and the line Lb
defined by the points P3 and P4.  Any points Pa and Pb on the lines La and
Lb therefore satisfy

	Pa = P1 + sa (P2 - P1)
	Pb = P3 + sb (P4 - P3)

for some values of the real numbers sa and sb.  To see if these two lines
La and Lb intersect, we wish to see if there are finite values sa and sb
for which

	Pa = Pb

Or, equivalently, we ask if there exists values of sa and sb for which
the equation

	P1 + sa (P2 - P1) = P3 + sb (P4 - P3)

holds.  If we confine ourselves to a two-dimensional plane, and take

	P1 = (x1, y1)
	P2 = (x2, y2)
	P3 = (x3, y3)
	P4 = (x4, y4)

we then find that we have two equations in two unknowns, sa and sb,

	x1 + sa ( x2 - x1 ) = x3 + sb ( x4 - x3 )
	y1 + sa ( y2 - y1 ) = y3 + sb ( y4 - y3 )

Solving these two equations for sa and sb yields,

	sa = [ ( y1 - y3 ) ( x4 - x3 ) - ( y4 - y3 ) ( x1 - x3 ) ] / d
	sb = [ ( y1 - y3 ) ( x2 - x1 ) - ( y2 - y1 ) ( x1 - x3 ) ] / d

where the denominator, d, is given by

	d = ( y4 - y3 ) ( x2 - x1 ) - ( y2 - y1 ) ( x4 - x3 )

Substituting these back for the point (x, y) of intersection gives

	x = x1 + sa ( x2 - x1 )
	y = y1 + sa ( y2 - y1 )

Note that

1. The lines are parallel when d = 0
2. The lines are coincident d = 0 and the numerators for sa & sb are zero
3. For line segments, sa and sb are in the range [0, 1]; any value outside
   that range indicates that the line segments do not intersect.
'''


def intersect(P1, P2, P3, P4):
    '''
    Determine if two line segments defined by the four points P1 & P2 and
    P3 & P4 intersect.  If they do intersect, then return the fractional
    point of intersection "sa" along the first line at which the
    intersection occurs.
    '''

    # Precompute these values -- note that we're basically shifting from
    #
    #		P = P1 + s (P2 - P1)
    #
    # to
    #
    # 		P = P1 + s D
    #
    # where D is a direction vector.  The solution remains the same of
    # course.  We'll just be computing D once for each line rather than
    # computing it a couple of times.

    D21x = P2[0] - P1[0]
    D21y = P2[1] - P1[1]
    D43x = P4[0] - P3[0]
    D43y = P4[1] - P3[1]

    # Denominator
    d = D21x * D43y - D21y * D43x

    # Return now if the denominator is zero
    if d == 0:
        return float(-1)

    # For our purposes, the first line segment given
    # by P1 & P2 is the LONG hatch line running through
    # the entire drawing.  And, P3 & P4 describe the
    # usually much shorter line segment from a polygon.
    # As such, we compute sb first as it's more likely
    # to indicate "no intersection".  That is, sa is
    # more likely to indicate an intersection with a
    # much a long line containing P3 & P4.

    nb = (P1[1] - P3[1]) * D21x - (P1[0] - P3[0]) * D21y

    # Could first check if abs(nb) > abs(d) or if
    # the signs differ.
    sb = float(nb) / float(d)
    if (sb < 0) or (sb > 1):
        return float(-1)

    na = (P1[1] - P3[1]) * D43x - (P1[0] - P3[0]) * D43y
    sa = float(na) / float(d)
    if (sa < 0) or (sa > 1):
        return float(-1)

    return sa

def interstices(P1, P2, paths, hatches, minGap=F_MINGAP_SMALL_VALUE):
    '''
    For the line L defined by the points P1 & P2, determine the segments
    of L which lie within the polygons described by the paths stored in
    "paths"

    P1 -- (x,y) coordinate [list]
    P2 -- (x,y) coordinate [list]
    paths -- Dictionary of all the paths to check for intersections

    When an intersection of the line L is found with a polygon edge, then
    the fractional distance along the line L is saved along with the
    lxml.etree node which contained the intersecting polygon edge.  This
    fractional distance is always in the range [0, 1].

    Once all polygons have been checked, the list of fractional distances
    corresponding to intersections is sorted and any duplicates removed.
    It is then assumed that the first intersection is the line L entering
    a polygon; the second intersection the line leaving the polygon.  This
    line segment defined by the first and second intersection points is
    thus a hatch fill line we sought to generate.  In general, our hatch
    fills become the line segments described by intersection i and i+1
    with i an odd value (1, 3, 5, ...).  Since we know the lxml.etree node
    corresponding to each intersection, we can then correlate the hatch
    fill lines to the graphical elements in the original SVG document.
    This enables us to group hatch lines with the elements being hatched.

    The hatch line segments are returned by populating a dictionary.
    The dictionary is keyed off of the lxml.etree node pointer.  Each
    dictionary value is a list of 4-tuples,

        (x1, y1, x2, y2)

    where (x1, y1) and (x2, y2) are the (x,y) coordinates of the line
    segment's starting and ending points.
    '''

    sa = []

    # P1 & P2 is the hatch line
    # P3 & P4 is the polygon edge to check
    for path in paths:
        for subpath in paths[path]:
            P3 = subpath[0]
            for P4 in subpath[1:]:
                s = intersect(P1, P2, P3, P4)
                if (s >= 0.0) and (s <= 1.0):
                    # Save this intersection point along the hatch line
                    sa.append((s, path))
                P3 = P4

    # Return now if there were no intersections
    if len(sa) == 0:
        return None

    # Sort the intersections
    sa.sort()

    # Remove duplicates intersections.  A common case where these arise
    # is when the hatch line passes through a vertex where one line segment
    # ends and the next one begins.

    # Having had sorted the data, it's trivial to just scan through
    # removing duplicates as we go and then truncating the array
    n = len(sa)
    ilast = i = 1
    last = sa[0]
    while i < n:
        if abs(sa[i][0] - last[0]) > F_MINGAP_SMALL_VALUE:
            sa[ilast] = last = sa[i]
            ilast += 1
        i += 1
    sa = sa[:ilast]
    if len(sa) < 2:
        return

    if minGap <= F_MINGAP_SMALL_VALUE:
        minGap = F_MINGAP_SMALL_VALUE

    # Now, entries with even valued indices into sa[] are where we start
    # a hatch line and odd valued indices where we end the hatch line.

    last_sa = None
    i = 0
    while i < (len(sa) - 1):
        # for i in range( 0, len( sa ) - 1, 2 ):

        # Mind the gap
        if abs(sa[i][0] - sa[i + 1][0]) > minGap:

            # This segment has a (relative) length which exceeds minGap

            if (last_sa is None) or (abs(sa[i][0] - last_sa[1][0]) > minGap):

                # And the gap between this segment and the prior segment
                # exceeds a (relative) length of minGap

                if sa[i][1] not in hatches:
                    hatches[sa[i][1]] = []

                x1 = P1[0] + sa[i][0] * (P2[0] - P1[0])
                y1 = P1[1] + sa[i][0] * (P2[1] - P1[1])
                x2 = P1[0] + sa[i + 1][0] * (P2[0] - P1[0])
                y2 = P1[1] + sa[i + 1][0] * (P2[1] - P1[1])

                hatches[sa[i][1]].append([[x1, y1], [x2, y2]])

            # Note we should not need to do the has_key() test, but let's
            # it anyway
            elif last_sa[0][1] in hatches:

                # The gap between this segment of the hatch line and the prior
                # segment is so small that we should join the two so as to
                # prevent creating a gap of relative length <= minGap

                # Replace the endpoint of the prior hatch line with the endpoint
                # of this hatch line

                x2 = P1[0] + sa[i + 1][0] * (P2[0] - P1[0])
                y2 = P1[1] + sa[i + 1][0] * (P2[1] - P1[1])
                hatches[last_sa[0][1]][-1][1] = [x2, y2]

            # Remember the relative start and end of this hatch segment
            last_sa = [sa[i], sa[i + 1]]

            i = i + 2

        else:
            i = i + 2  # Skip this hatch segment, but note that we must skip the segment entirely,
        # not just skip its beginning point

    # Ignore cases where the prior segment was short, this segment was
    # short, and the gap between them was short but we might just want
    # to combine them into one long segment.  That's indeed a possible
    # choice, but so may be the choice of dropping them silently in the
    # hatch segment wastebasket.

def inverseTransform(tran):
    '''
    An SVG transform matrix looks like

        [  a   c   e  ]
        [  b   d   f  ]
        [  0   0   1  ]

    And it's inverse is

        [  d   -c   cf - de  ]
        [ -b    a   be - af  ] * ( ad - bc ) ** -1
        [  0    0      1     ]

    And, no reasonable 2d coordinate transform will have
    the products ad and bc equal.

    SVG represents the transform matrix column by column as
    matrix(a b c d e f) while Inkscape extensions store the
    transform matrix as

        [[a, c, e], [b, d, f]]

    To invert the transform stored Inskcape style, we wish to
    produce

        [[d/D, -c/D, (cf - de)/D], [-b/D, a/D, (be-af)/D]]

    where

        D = 1 / (ad - bc)
    '''

    D = tran[0][0] * tran[1][1] - tran[1][0] * tran[0][1]
    if D == 0:
        return None

    return [[tran[1][1] / D, -tran[0][1] / D,
             (tran[0][1] * tran[1][2] - tran[1][1] * tran[0][2]) / D],
            [-tran[1][0] / D, tran[0][0] / D,
             (tran[1][0] * tran[0][2] - tran[0][0] * tran[1][2]) / D]]

def parseLengthWithUnits(str):
    '''
    Parse an SVG value which may or may not have units attached
    This version is greatly simplified in that it only allows: no units,
    units of px, and units of %.  Everything else, it returns None for.
    There is a more general routine to consider in scour.py if more
    generality is ever needed.
    '''

    u = 'px'
    s = str.strip()
    if s[-2:] == 'px':
        s = s[:-2]
    elif s[-1:] == '%':
        u = '%'
        s = s[:-1]

    try:
        v = float(s)
    except:
        return None, None

    return v, u

# Lifted with impunity from eggbot.py

def subdivideCubicPath(sp, flat, i=1):
    """
    Break up a bezier curve into smaller curves, each of which
    is approximately a straight line within a given tolerance
    (the "smoothness" defined by [flat]).

    This is a modified version of cspsubdiv.cspsubdiv() rewritten
    to avoid recurrence.
    """

    while True:
        while True:
            if i >= len(sp):
                return

            p0 = sp[i - 1][1]
            p1 = sp[i - 1][2]
            p2 = sp[i][0]
            p3 = sp[i][1]

            b = (p0, p1, p2, p3)

            #if cspsubdiv.maxdist(b) > flat:
                #break

            i += 1

        one, two = bezmisc.beziersplitatt(b, 0.5)
        sp[i - 1][2] = one[1]
        sp[i][0] = two[2]
        p = [one[2], one[3], two[1]]
        sp[i:1] = [p]


def distanceSquared(P1, P2):
    '''
    Pythagorean distance formula WITHOUT the square root.  Since
    we just want to know if the distance is less than some fixed
    fudge factor, we can just square the fudge factor once and run
    with it rather than compute square roots over and over.
    '''

    dx = P2[0] - P1[0]
    dy = P2[1] - P1[1]

    return (dx * dx + dy * dy)


class Eggbot_Hatch(inkex.Effect):

    def __init__(self):

        inkex.Effect.__init__(self)

        self.xmin, self.ymin = (float(0), float(0))
        self.xmax, self.ymax = (float(0), float(0))
        self.paths = {}
        self.grid = []
        self.hatches = {}
        self.transforms = {}
        self.minGap = float(0)

        # For handling an SVG viewbox attribute, we will need to know the
        # values of the document's <svg> width and height attributes as well
        # as establishing a transform from the viewbox to the display.

        canvas_w = (Entry_box_6.get())
        canvas_h = (Entry_box_7.get())
        N_PAGE_WIDTH = canvas_w
        N_PAGE_HEIGHT = canvas_h
        self.docWidth = float(N_PAGE_WIDTH)
        self.docHeight = float(N_PAGE_HEIGHT)

        self.docTransform = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0]]

        self.OptionParser.add_option(
            "--reducePenLifts", action="store", dest="reducePenLifts",
            type="inkbool", default=False,
            help="Reduce plotting time by joining some hatches")
        self.OptionParser.add_option(
            "--crossHatch", action="store", dest="crossHatch",
            type="inkbool", default=False,
            help="Generate a cross hatch pattern")
        self.OptionParser.add_option(
            "--hatchAngle", action="store", type="float",
            dest="hatchAngle", default=90.0,
            help="Angle of inclination for hatch lines")
        self.OptionParser.add_option(
            "--hatchSpacing", action="store", type="float",
            dest="hatchSpacing", default=2.0,
            help="Spacing between hatch lines")
        self.OptionParser.add_option(
            "--tolerance", action="store", type="float",
            dest="tolerance", default=3.0,
            help="Allowed deviation from original paths")
        self.OptionParser.add_option(
            "--minGap", action="store", type="float",
            dest="minGap", default=1.0,
            help="Minimum length of hatch segments and gaps")
        self.OptionParser.add_option("--tab",  # NOTE: value is not used.
                                     action="store", type="string", dest="tab", default="splash",
                                     help="The active tab when Apply was pressed")

    def getLength(self, name, default):

        '''
        Get the <svg> attribute with name "name" and default value "default"
        Parse the attribute into a value and associated units.  Then, accept
        no units (''), units of pixels ('px'), and units of percentage ('%').
        '''

        str = self.document.getroot().get(name)
        if str:
            v, u = parseLengthWithUnits(str)
            if not v:
                # Couldn't parse the value
                return None
            elif (u == '') or (u == 'px'):
                return v
            elif u == '%':
                return float(default) * v / 100.0
            else:
                # Unsupported units
                return None
        else:
            # No width specified; assume the default value
            return float(default)

    def getDocProps(self):

        '''
        Get the document's height and width attributes from the <svg> tag.
        Use a default value in case the property is not present or is
        expressed in units of percentages.
        '''

        self.docHeight = self.getLength('height', N_PAGE_HEIGHT)
        self.docWidth = self.getLength('width', N_PAGE_WIDTH)
        if (self.docHeight == None) or (self.docWidth == None):
            return False
        else:
            return True

    def handleViewBox(self):

        '''
        Set up the document-wide transform in the event that the document has an SVG viewbox
        '''

        if self.getDocProps():
            viewbox = self.document.getroot().get('viewBox')
            if viewbox:
                vinfo = viewbox.strip().replace(',', ' ').split(' ')
                if (vinfo[2] != 0) and (vinfo[3] != 0):
                    sx = self.docWidth / float(vinfo[2])
                    sy = self.docHeight / float(vinfo[3])
                    self.docTransform = simpletransform.parseTransform('scale(%f,%f)' % (sx, sy))

    def addPathVertices(self, path, node=None, transform=None):

        '''
        Decompose the path data from an SVG element into individual
        subpaths, each starting with an absolute move-to (x, y)
        coordinate followed by one or more absolute line-to (x, y)
        coordinates.  Each subpath is stored as a list of (x, y)
        coordinates, with the first entry understood to be a
        move-to coordinate and the rest line-to coordinates.  A list
        is then made of all the subpath lists and then stored in the
        self.paths dictionary using the path's lxml.etree node pointer
        as the dictionary key.
        '''

        if (not path) or (len(path) == 0):
            return

        # parsePath() may raise an exception.  This is okay
        sp = simplepath.parsePath(path)
        if (not sp) or (len(sp) == 0):
            return

        # Get a cubic super duper path
        p = cubicsuperpath.CubicSuperPath(sp)
        if (not p) or (len(p) == 0):
            return

        # Apply any transformation
        if transform != None:
            simpletransform.applyTransformToPath(transform, p)

        # Now traverse the simplified path
        subpaths = []
        subpath_vertices = []
        for sp in p:
            # We've started a new subpath
            # See if there is a prior subpath and whether we should keep it
            if len(subpath_vertices):
                if distanceSquared(subpath_vertices[0], subpath_vertices[-1]) < 1:
                    # Keep the prior subpath: it appears to be a closed path
                    subpaths.append(subpath_vertices)
            subpath_vertices = []
            tolerance_slider = Entry_box_5.get()
            float_tolerance_slider = float(tolerance_slider)
            self.options.tolerance = float_tolerance_slider

            subdivideCubicPath(sp, float(self.options.tolerance / 100))
            for csp in sp:
                # Add this vertex to the list of vetices
                subpath_vertices.append(csp[1])

        # Handle final subpath
        if len(subpath_vertices):
            if distanceSquared(subpath_vertices[0], subpath_vertices[-1]) < 1:
                # Path appears to be closed so let's keep it
                subpaths.append(subpath_vertices)

        # Empty path?
        if len(subpaths) == 0:
            return

        # And add this path to our dictionary of paths
        self.paths[node] = subpaths

        # And save the transform for this element in a dictionary keyed
        # by the element's lxml node pointer
        self.transforms[node] = transform

    def getBoundingBox(self):

        '''
        Determine the bounding box for our collection of polygons
        '''

        self.xmin, self.xmax = float(1.0E70), float(-1.0E70)
        self.ymin, self.ymax = float(1.0E70), float(-1.0E70)

        for path in self.paths:
            for subpath in self.paths[path]:
                for vertex in subpath:
                    if vertex[0] < self.xmin:
                        self.xmin = vertex[0]
                    elif vertex[0] > self.xmax:
                        self.xmax = vertex[0]
                    if vertex[1] < self.ymin:
                        self.ymin = vertex[1]
                    elif vertex[1] > self.ymax:
                        self.ymax = vertex[1]

    def recursivelyTraverseSvg(self, aNodeList,
                               matCurrent=[[1.0, 0.0, 0.0], [0.0, 1.0, 0.0]],
                               parent_visibility='visible'):

        '''
        Recursively walk the SVG document, building polygon vertex lists
        for each graphical element we support.

        Rendered SVG elements:
            <circle>, <ellipse>, <line>, <path>, <polygon>, <polyline>, <rect>

        Supported SVG elements:
            <group>, <use>

        Ignored SVG elements:
            <defs>, <eggbot>, <metadata>, <namedview>, <pattern>

        All other SVG elements trigger an error (including <text>)
        '''

        for node in aNodeList:

            # Ignore invisible nodes
            v = node.get('visibility', parent_visibility)
            if v == 'inherit':
                v = parent_visibility
            if v == 'hidden' or v == 'collapse':
                pass

            # first apply the current matrix transform to this node's tranform
            matNew = simpletransform.composeTransform(matCurrent,
                                                      simpletransform.parseTransform(node.get("transform")))

            if node.tag == inkex.addNS('g', 'svg') or node.tag == 'g':

                self.recursivelyTraverseSvg(node, matNew, parent_visibility=v)

            elif node.tag == inkex.addNS('use', 'svg') or node.tag == 'use':

                # A <use> element refers to another SVG element via an xlink:href="#blah"
                # attribute.  We will handle the element by doing an XPath search through
                # the document, looking for the element with the matching id="blah"
                # attribute.  We then recursively process that element after applying
                # any necessary (x,y) translation.
                #
                # Notes:
                #  1. We ignore the height and width attributes as they do not apply to
                #     path-like elements, and
                #  2. Even if the use element has visibility="hidden", SVG still calls
                #     for processing the referenced element.  The referenced element is
                #     hidden only if its visibility is "inherit" or "hidden".

                refid = node.get(inkex.addNS('href', 'xlink'))
                if not refid:
                    pass

                # [1:] to ignore leading '#' in reference
                path = '//*[@id="%s"]' % refid[1:]
                refnode = node.xpath(path)
                if refnode:
                    x = float(node.get('x', '0'))
                    y = float(node.get('y', '0'))
                    # Note: the transform has already been applied
                    if (x != 0) or (y != 0):
                        matNew2 = composeTransform(matNew, parseTransform('translate(%f,%f)' % (x, y)))
                    else:
                        matNew2 = matNew
                    v = node.get('visibility', v)
                    self.recursivelyTraverseSvg(refnode, matNew2, parent_visibility=v)

            elif node.tag == inkex.addNS('path', 'svg'):

                path_data = node.get('d')
                if path_data:
                    self.addPathVertices(path_data, node, matNew)

            elif node.tag == inkex.addNS('rect', 'svg') or node.tag == 'rect':

                # Manually transform
                #
                #    <rect x="X" y="Y" width="W" height="H"/>
                #
                # into
                #
                #    <path d="MX,Y lW,0 l0,H l-W,0 z"/>
                #
                # I.e., explicitly draw three sides of the rectangle and the
                # fourth side implicitly

                # Create a path with the outline of the rectangle
                x = float(node.get('x'))
                y = float(node.get('y'))
                if (not x) or (not y):
                    pass
                w = float(node.get('width', '0'))
                h = float(node.get('height', '0'))
                a = []
                a.append(['M ', [x, y]])
                a.append([' l ', [w, 0]])
                a.append([' l ', [0, h]])
                a.append([' l ', [-w, 0]])
                a.append([' Z', []])
                self.addPathVertices(simplepath.formatPath(a), node, matNew)

            elif node.tag == inkex.addNS('line', 'svg') or node.tag == 'line':

                # Convert
                #
                #   <line x1="X1" y1="Y1" x2="X2" y2="Y2/>
                #
                # to
                #
                #   <path d="MX1,Y1 LX2,Y2"/>

                x1 = float(node.get('x1'))
                y1 = float(node.get('y1'))
                x2 = float(node.get('x2'))
                y2 = float(node.get('y2'))
                if (not x1) or (not y1) or (not x2) or (not y2):
                    pass
                a = []
                a.append(['M ', [x1, y1]])
                a.append([' L ', [x2, y2]])
                self.addPathVertices(simplepath.formatPath(a), node, matNew)

            elif node.tag == inkex.addNS('polyline', 'svg') or node.tag == 'polyline':

                # Convert
                #
                #  <polyline points="x1,y1 x2,y2 x3,y3 [...]"/>
                #
                # to
                #
                #   <path d="Mx1,y1 Lx2,y2 Lx3,y3 [...]"/>
                #
                # Note: we ignore polylines with no points

                pl = node.get('points', '').strip()
                if pl == '':
                    pass

                pa = pl.split()
                d = "".join(["M " + pa[i] if i == 0 else " L " + pa[i] for i in range(0, len(pa))])
                self.addPathVertices(d, node, matNew)

            elif node.tag == inkex.addNS('polygon', 'svg') or node.tag == 'polygon':

                # Convert
                #
                #  <polygon points="x1,y1 x2,y2 x3,y3 [...]"/>
                #
                # to
                #
                #   <path d="Mx1,y1 Lx2,y2 Lx3,y3 [...] Z"/>
                #
                # Note: we ignore polygons with no points

                pl = node.get('points', '').strip()
                if pl == '':
                    pass

                pa = pl.split()
                d = "".join(["M " + pa[i] if i == 0 else " L " + pa[i] for i in range(0, len(pa))])
                d += " Z"
                self.addPathVertices(d, node, matNew)

            elif node.tag == inkex.addNS('ellipse', 'svg') or \
                    node.tag == 'ellipse' or \
                    node.tag == inkex.addNS('circle', 'svg') or \
                    node.tag == 'circle':

                # Convert circles and ellipses to a path with two 180 degree arcs.
                # In general (an ellipse), we convert
                #
                #   <ellipse rx="RX" ry="RY" cx="X" cy="Y"/>
                #
                # to
                #
                #   <path d="MX1,CY A RX,RY 0 1 0 X2,CY A RX,RY 0 1 0 X1,CY"/>
                #
                # where
                #
                #   X1 = CX - RX
                #   X2 = CX + RX
                #
                # Note: ellipses or circles with a radius attribute of value 0 are ignored

                if node.tag == inkex.addNS('ellipse', 'svg') or node.tag == 'ellipse':
                    rx = float(node.get('rx', '0'))
                    ry = float(node.get('ry', '0'))
                else:
                    rx = float(node.get('r', '0'))
                    ry = rx
                if rx == 0 or ry == 0:
                    pass

                cx = float(node.get('cx', '0'))
                cy = float(node.get('cy', '0'))
                x1 = cx - rx
                x2 = cx + rx
                d = 'M %f,%f ' % (x1, cy) + \
                    'A %f,%f ' % (rx, ry) + \
                    '0 1 0 %f,%f ' % (x2, cy) + \
                    'A %f,%f ' % (rx, ry) + \
                    '0 1 0 %f,%f' % (x1, cy)
                self.addPathVertices(d, node, matNew)

            elif node.tag == inkex.addNS('pattern', 'svg') or node.tag == 'pattern':

                pass

            elif node.tag == inkex.addNS('metadata', 'svg') or node.tag == 'metadata':

                pass

            elif node.tag == inkex.addNS('defs', 'svg') or node.tag == 'defs':

                pass

            elif node.tag == inkex.addNS('namedview', 'sodipodi') or node.tag == 'namedview':

                pass

            elif node.tag == inkex.addNS('eggbot', 'svg') or node.tag == 'eggbot':

                pass

            elif node.tag == inkex.addNS('text', 'svg') or node.tag == 'text':

                inkex.errormsg('Warning: unable to draw text, please convert it to a path first.')

                pass

            elif not isinstance(node.tag, str):

                pass

            else:

                inkex.errormsg('Warning: unable to draw object <%s>, please convert it to a path first.' % node.tag)
                pass

    def joinFillsWithNode(self, node, stroke_width, path):

        '''
        Generate a SVG <path> element containing the path data "path".
        Then put this new <path> element into a <group> with the supplied
        node.  This means making a new <group> element and moving node
        under it with the new <path> as a sibling element.
        '''

        if (not path) or (len(path) == 0):
            return

        # Make a new SVG <group> element whose parent is the parent of node
        parent = node.getparent()
        # was: if not parent:
        if parent is None:
            parent = self.document.getroot()
        g = inkex.etree.SubElement(parent, inkex.addNS('g', 'svg'))

        # Move node to be a child of this new <g> element
        g.append(node)

        # Now make a <path> element which contains the hatches & is a child
        # of the new <g> element
        strokewidht = Entry_box_4.get()
        float_stroke_width = float(strokewidht)
        color = Entry_box_8.get()
        style = {'stroke': color, 'fill': 'none', 'stroke-width': '%f' % float_stroke_width}
        line_attribs = {'style': simplestyle.formatStyle(style), 'd': path}
        tran = node.get('transform')
        if (tran != None) and (tran != ''):
            line_attribs['transform'] = tran
        inkex.etree.SubElement(g, inkex.addNS('path', 'svg'), line_attribs)

    def makeHatchGrid(self, angle, spacing, init=True):

        '''
        Build a grid of hatch lines which encompasses the entire bounding
        box of the graphical elements we are to hatch.

        1. Figure out the bounding box for all of the graphical elements
        2. Pick a rectangle larger than that bounding box so that we can
           later rotate the rectangle and still have it cover the bounding
           box of the graphical elements.
        3. Center the rectangle of 2 on the origin (0, 0).
        4. Build the hatch line grid in this rectangle.
        5. Rotate the rectangle by the hatch angle.
        6. Translate the center of the rotated rectangle, (0, 0), to be
           the center of the bounding box for the graphical elements.
        7. We now have a grid of hatch lines which overlay the graphical
           elements and can now be intersected with those graphical elements.
        '''

        # If this is the first call, do some one time initializations
        # When generating cross hatches, we may be called more than once
        if init:
            self.getBoundingBox()
            self.grid = []

        # Determine the width and height of the bounding box containing
        # all the polygons to be hatched
        w = self.xmax - self.xmin
        h = self.ymax - self.ymin

        # Nice thing about rectangles is that the diameter of the circle
        # encompassing them is the length the rectangle's diagonal...
        r = math.sqrt(w * w + h * h) / 2.0

        # Length of a hatch line will be 2r
        # We wish to convert the number of pixels considered insignificant
        # to a unitless, fractional length of a hatch line.  The length of
        # a hatch line is 2r pixels.  So,

        minGap_slider = Entry_box_3.get()
        float_minGap_slider = float(minGap_slider)
        self.options.minGap = float_minGap_slider

        self.minGap = self.options.minGap / (2.0 * r)

        # Now generate hatch lines within the square
        # centered at (0, 0) and with side length at least d

        # While we could generate these lines running back and forth,
        # that makes for weird behavior later when applying odd/even
        # rules AND there are nested polygons.  Instead, when we
        # generate the SVG <path> elements with the hatch line
        # segments, we can do the back and forth weaving.

        # Rotation information
        ca = math.cos(math.radians(90 - angle))
        sa = math.sin(math.radians(90 - angle))

        # Translation information
        cx = self.xmin + (w / 2)
        cy = self.ymin + (h / 2)

        # Since the spacing may be fractional (e.g., 6.5), we
        # don't try to use range() or other integer iterator
        spacing = float(abs(spacing))
        i = -r
        while i <= r:
            # Line starts at (i, -r) and goes to (i, +r)
            x1 = cx + (i * ca) + (r * sa)  # i * ca - (-r) * sa
            y1 = cy + (i * sa) - (r * ca)  # i * sa + (-r) * ca
            x2 = cx + (i * ca) - (r * sa)  # i * ca - (+r) * sa
            y2 = cy + (i * sa) + (r * ca)  # i * sa + (+r) * ca
            i += spacing
            # Remove any potential hatch lines which are entirely
            # outside of the bounding box
            if ((x1 < self.xmin) and (x2 < self.xmin)) or \
                    ((x1 > self.xmax) and (x2 > self.xmax)):
                continue
            if ((y1 < self.ymin) and (y2 < self.ymin)) or \
                    ((y1 > self.ymax) and (y2 > self.ymax)):
                continue
            self.grid.append((x1, y1, x2, y2))

    def effect(self):

        # Viewbox handling
        self.handleViewBox()

        # Build a list of the vertices for the document's graphical elements
        if self.options.ids:
            # Traverse the selected objects
            for id in self.options.ids:
                self.recursivelyTraverseSvg([self.selected[id]], self.docTransform)
        else:
            # Traverse the entire document
            self.recursivelyTraverseSvg(self.document.getroot(), self.docTransform)

        Hatch_spacing = (Entry_box_1.get())
        float_Hatch_spacing = float(Hatch_spacing)

        if  root.Crosshatch.get() =="1":
            self.options.crossHatch = True


        Hatch_angle = (Entry_box_2.get())
        float_Hatch_angle = float(Hatch_angle)
        self.options.hatchAngle = float_Hatch_angle

        # Build a grid of possible hatch lines
        self.makeHatchGrid(float(self.options.hatchAngle),
                           float(float_Hatch_spacing), True)

        if self.options.crossHatch:
            self.makeHatchGrid(float(self.options.hatchAngle + 90),
                               float(float_Hatch_spacing), False)

        # Now loop over our hatch lines looking for intersections
        for h in self.grid:
            interstices((h[0], h[1]), (h[2], h[3]), self.paths, self.hatches, self.minGap)

        # Target stroke width will be (doc width + doc height) / 2 / 1000
        # stroke_width_target = ( self.docHeight + self.docWidth ) / 2000
        stroke_width_target = 1

        # Each hatch line stroke will be within an SVG object which may
        # be subject to transforms.  So, on an object by object basis,
        # we need to transform our target width to a width suitable
        # for that object (so that after the object and its hatches are
        # transformed, the result has the desired width).

        # To aid in the process, we use a diagonal line segment of length
        # stroke_width_target.  We then run this segment through an object's
        # inverse transform and see what the resulting length of the inversely
        # transformed segment is.  We could, alternatively, look at the
        # x and y scaling factors in the transform and average them.
        s = stroke_width_target / math.sqrt(2)

        # Now, dump the hatch fills sorted by which document element
        # they correspond to.  This is made easy by the fact that we
        # saved the information and used each element's lxml.etree node
        # pointer as the dictionary key under which to save the hatch
        # fills for that node.

        absoluteLineSegments = {}
        nAbsoluteLineSegmentCount = 0
        nPenLifts = 0
        # To implement
        for key in self.hatches:
            direction = True
            if key in self.transforms:
                transform = inverseTransform(self.transforms[key])
                # Determine the scaled stroke width for a hatch line
                # We produce a line segment of unit length, transform
                # its endpoints and then determine the length of the
                # resulting line segment.
                pt1 = [0, 0]
                pt2 = [s, s]
                simpletransform.applyTransformToPoint(transform, pt1)
                simpletransform.applyTransformToPoint(transform, pt2)
                dx = pt2[0] - pt1[0]
                dy = pt2[1] - pt1[1]
                stroke_width = math.sqrt(dx * dx + dy * dy)
            else:
                transform = None
                stroke_width = float(1.0)

            path = ''
            if root.Ends.get() == "1":
                self.options.reducePenLifts = True

            if not self.options.reducePenLifts:
                for segment in self.hatches[key]:
                    if len(segment) < 2:
                        continue
                    pt1 = segment[0]
                    pt2 = segment[1]
                    # Okay, we're going to put these hatch lines into the same
                    # group as the element they hatch.  That element is down
                    # some chain of SVG elements, some of which may have
                    # transforms attached.  But, our hatch lines have been
                    # computed assuming that those transforms have already
                    # been applied (since we had to apply them so as to know
                    # where this element is on the page relative to other
                    # elements and their transforms).  So, we need to invert
                    # the transforms for this element and then either apply
                    # that inverse transform here and now or set it in a
                    # transform attribute of the <path> element.  Having it
                    # set in the path element seems a bit counterintuitive
                    # after the fact (i.e., what's this tranform here for?).
                    # So, we compute the inverse transform and apply it here.
                    if transform != None:
                        simpletransform.applyTransformToPoint(transform, pt1)
                        simpletransform.applyTransformToPoint(transform, pt2)
                    # Now generate the path data for the <path>
                    if direction:
                        # Go this direction
                        path += 'M %f,%f l %f,%f ' % \
                                (pt1[0], pt1[1], pt2[0] - pt1[0], pt2[1] - pt1[1])
                    else:
                        # Or go this direction
                        path += 'M %f,%f l %f,%f ' % \
                                (pt2[0], pt2[1], pt1[0] - pt2[0], pt1[1] - pt2[1])
                    direction = not direction
                self.joinFillsWithNode(key, stroke_width, path[:-1])

            else:  # if not self.options.reducePenLifts:
                for segment in self.hatches[key]:
                    if len(segment) < 2:
                        continue
                    pt1 = segment[0]
                    pt2 = segment[1]
                    # Okay, we're going to put these hatch lines into the same
                    # group as the element they hatch.  That element is down
                    # some chain of SVG elements, some of which may have
                    # transforms attached.  But, our hatch lines have been
                    # computed assuming that those transforms have already
                    # been applied (since we had to apply them so as to know
                    # where this element is on the page relative to other
                    # elements and their transforms).  So, we need to invert
                    # the transforms for this element and then either apply
                    # that inverse transform here and now or set it in a
                    # transform attribute of the <path> element.  Having it
                    # set in the path element seems a bit counterintuitive
                    # after the fact (i.e., what's this tranform here for?).
                    # So, we compute the inverse transform and apply it here.
                    if transform != None:
                        simpletransform.applyTransformToPoint(transform, pt1)
                        simpletransform.applyTransformToPoint(transform, pt2)

                    # Now generate the path data for the <path>
                    # BUT we want to combine as many paths as possible.
                    # In order to combine paths, we need to know all of the segments.
                    # The solution to this conundrum is to generate all segments,
                    # but instead of drawing them into the path, we put them in
                    # an array where they'll be available for random access
                    # by our anti-pen-lift algorithm
                    absoluteLineSegments[nAbsoluteLineSegmentCount] = [pt1, pt2,
                                                                       False]  # False indicates that segment has not yet been drawn
                    nAbsoluteLineSegmentCount += 1
                # for segment in self.hatches[key]:

                # Now have a nice juicy buffer full of line segments with absolute coordinates
                #				inkex.errormsg( 'Have %i line segments.' % nAbsoluteLineSegmentCount )
                for count in range(nAbsoluteLineSegmentCount):  # This is the entire range of segments
                    if (not absoluteLineSegments[count][2]):  # Test whether this segment has been drawn
                        # Has not been drawn yet
                        path = ''
                        deltaX = absoluteLineSegments[count][1][0] - absoluteLineSegments[count][0][
                            0]  # final point (pt2) X minus initial point (pt1) X
                        deltaY = absoluteLineSegments[count][1][1] - absoluteLineSegments[count][0][
                            1]  # final point (pt2) Y minus initial point (pt1) Y
                        path += 'M %f,%f l %f,%f ' % \
                                (absoluteLineSegments[count][0][0], absoluteLineSegments[count][0][1], \
                                 deltaX, deltaY)  # delta is from initial point
                        absoluteLineSegments[count][2] = True  # True flags that this line segment has been
                        # added to the path to be drawn, so should
                        # no longer be a candidate for a relative move.
                        nPenLifts += 1
                        # Now comes the speedup logic:
                        # We've just drawn a segment starting at an absolute, not relative, position.
                        # It was drawn from pt1 to pt2.
                        # Look for an as-yet-not-drawn segment which has a beginning or ending
                        # point "near" the end point of this absolute draw, and leave the pen down
                        # while moving to and then drawing this found line.
                        # Do this recursively, marking each segment True to show that
                        # it has been "drawn" already.
                        # pt2 is the reference point, ie. the point from which the next segment will start
                        # '''						path = self.recursivelyAppendNearbySegmentIfAny( absoluteLineSegments[count][1], nAbsoluteLineSegmentCount, absoluteLineSegments, path )
                        path = self.recursivelyAppendNearbySegmentIfAny(count, 1, nAbsoluteLineSegmentCount,
                                                                        absoluteLineSegments, path)

                        self.joinFillsWithNode(key, stroke_width, path[:-1])
                # if ( not absoluteLineSegments[count][2] ):
            # for count in range( nAbsoluteLineSegmentCount ):

    #				inkex.errormsg( 'Number of pen lifts %i'  %  nPenLifts )
    # if not self.options.reducePenLifts:
    # for key in self.hatches:

    # inkex.errormsg("Elapsed CPU time was %f" % (time.clock()-self.t0))

    #	def recursivelyAppendNearbySegmentIfAny( self, ptReference, nAbsoluteLineSegmentCount, absoluteLineSegments, cumulativePath ):
    def recursivelyAppendNearbySegmentIfAny(self, nReferenceSegmentCount, nReferenceEndIndex, nAbsoluteLineSegmentCount,
                                            absoluteLineSegments, cumulativePath):

        bFoundSegmentToAdd = False  # default assumption
        fProposedNeighborhoodRadiusSquared = self.options.hatchSpacing * self.options.hatchSpacing * 2
        # The multiplier of 2 generates a radius of sqrt(2) times the hatch spacing.
        # This means that a point will be accepted if it is no more
        # than 45 degrees away from reference

        # Look through all possibilities to choose the closest
        nCountAtClosest = -1
        fClosestDistance = 123456.0
        for count in range(nAbsoluteLineSegmentCount):  # investigate all segments
            if (not absoluteLineSegments[count][2]):
                # This segment currently undrawn, so it is a candidate for a path extension

                # Need to check both ends of each and every proposed segment until we find one in the neighborhood
                # Define pt2 in the reference as the end which we want to extend
                # First initial end of test segment (aka pt1) vs final end (aka pt2) of reference segment
                deltaX = absoluteLineSegments[count][0][0] - \
                         absoluteLineSegments[nReferenceSegmentCount][nReferenceEndIndex][
                             0]  # proposed initial pt1 X minus existing final pt1 X
                deltaY = absoluteLineSegments[count][0][1] - \
                         absoluteLineSegments[nReferenceSegmentCount][nReferenceEndIndex][
                             1]  # proposed initial pt1 Y minus existing final pt1 Y

                if ((deltaX * deltaX + deltaY * deltaY) < fProposedNeighborhoodRadiusSquared):
                    nNewSegmentInitialEndIndex = 0  # pt1
                    nNewSegmentFinalEndIndex = 1  # pt2

                    bReferenceIsReversed = False  # Because we're testing against pt1 of the proposed segment
                    bFoundSegmentToAdd = True
                    break

                else:
                    # Initial end of test segment failed (aka pt1), try final end of test (aka pt2) vs final end of reference segment
                    deltaX = absoluteLineSegments[count][1][0] - \
                             absoluteLineSegments[nReferenceSegmentCount][nReferenceEndIndex][
                                 0]  # proposed initial point X minus existing final point X
                    deltaY = absoluteLineSegments[count][1][1] - \
                             absoluteLineSegments[nReferenceSegmentCount][nReferenceEndIndex][
                                 1]  # proposed initial point Y minus existing final point Y
                    if ((deltaX * deltaX + deltaY * deltaY) < fProposedNeighborhoodRadiusSquared):
                        nNewSegmentInitialEndIndex = 1  # pt2
                        nNewSegmentFinalEndIndex = 0  # pt1

                        bFoundSegmentToAdd = True
                        break

        # if ( not absoluteLineSegments[2] ):
        # for count in range( nAbsoluteLineSegmentCount ):

        if (not bFoundSegmentToAdd):
            return cumulativePath  # No undrawn segments were suitable for appending
        else:
            # count is the index of the segment to be appended.
            # nNewSegmentInitialEndIndex is 0 for connecting to pt1,
            # and is 1 for connecting to pt2

            # First, move pen to initial end (may be either its pt1 or its pt2) of new segment

            if 0:  # if 0: or maybe if 1:
                # The method of the next line makes abrupt angle changes at the corners, which
                # is not ideal from the standpoint of shaking the pen.
                cumulativePath += '%f,%f ' % (deltaX, deltaY)
            else:  # if 0: or maybe if 1:
                '''
                # Insert a bezier curve for this transition element
                # To accomplish this, we need information on the incoming and outgoing segments.
                # Specifically, we need to know the lengths and angles of the segments in
                # order to decide on control points.

                # Temporarily just assume the angle change is pi, just to make sure
                # this method will work:
                '''
                fIncomingDeltaX = absoluteLineSegments[nReferenceSegmentCount][nReferenceEndIndex][0] - \
                                  absoluteLineSegments[nReferenceSegmentCount][not nReferenceEndIndex][
                                      0]  # ''' fix this up to use indexed array, rather than different names
                fIncomingDeltaY = absoluteLineSegments[nReferenceSegmentCount][nReferenceEndIndex][1] - \
                                  absoluteLineSegments[nReferenceSegmentCount][not nReferenceEndIndex][
                                      1]  # ''' fix this up to use indexed array, rather than different names
                # The outgoing deltas are based on the reverse direction of the segment, i.e. the segment pointing back to the joiner bezier curve
                fOutgoingDeltaX = absoluteLineSegments[count][nNewSegmentInitialEndIndex][0] - \
                                  absoluteLineSegments[count][nNewSegmentFinalEndIndex][
                                      0]  # index is [count][start point = 0, final point = 1][0=x, 1=y]
                # '''				inkex.errormsg( 'fOutgoingDeltaX= %f  term 1= %f  term 2= %f' % ( fOutgoingDeltaX, absoluteLineSegments[count][0][0], absoluteLineSegments[count][1][0] ) )
                fOutgoingDeltaY = absoluteLineSegments[count][nNewSegmentInitialEndIndex][1] - \
                                  absoluteLineSegments[count][nNewSegmentFinalEndIndex][1]
                # Now, we know we want the control points to be on a projection of each segment,
                # in order that there be no abrupt change of plotting angle.  The question is, how
                # far beyond the endpoint should we place the control point.  The answer is undoubtedly
                # a function of the angular discrepancy between the two lines.
                # What this function is, I do not know, so will ignore the problem for the moment
                # by just using a fixed distance.
                ptRelativeControlPointIncoming = self.RelativeControlPointPosition(
                    F_MAXIMUM_BEZIER_CONTROL_POINT_DISTANCE, fIncomingDeltaX, fIncomingDeltaY, 0, 0)
                ptRelativeControlPointOutgoing = self.RelativeControlPointPosition(
                    F_MAXIMUM_BEZIER_CONTROL_POINT_DISTANCE, fOutgoingDeltaX, fOutgoingDeltaY, deltaX, deltaY)

                cumulativePath += 'c %f,%f %f,%f %f,%f l ' % \
                                  (ptRelativeControlPointIncoming[0], \
                                   ptRelativeControlPointIncoming[1], \
                                   ptRelativeControlPointOutgoing[0], \
                                   ptRelativeControlPointOutgoing[1], \
                                   deltaX, \
                                   deltaY)
            # if 0: or maybe if 1:

            # Next, move pen in appropriate direction to draw the new segment, given that
            # we have just moved to the initial end of the new segment.
            deltaX = absoluteLineSegments[count][nNewSegmentFinalEndIndex][0] - \
                     absoluteLineSegments[count][nNewSegmentInitialEndIndex][0]
            deltaY = absoluteLineSegments[count][nNewSegmentFinalEndIndex][1] - \
                     absoluteLineSegments[count][nNewSegmentInitialEndIndex][1]
            cumulativePath += '%f,%f ' % (deltaX, deltaY)
            # '''			inkex.errormsg( cumulativePath )
            # Mark this segment as drawn
            absoluteLineSegments[count][2] = True

            # '''			cumulativePath = self.recursivelyAppendNearbySegmentIfAny( absoluteLineSegments[count][nNewSegmentFinalEndIndex], nAbsoluteLineSegmentCount, absoluteLineSegments, cumulativePath )
            cumulativePath = self.recursivelyAppendNearbySegmentIfAny(count, nNewSegmentFinalEndIndex,
                                                                      nAbsoluteLineSegmentCount, absoluteLineSegments,
                                                                      cumulativePath)
            return cumulativePath

    def RelativeControlPointPosition(self, distance, fDeltaX, fDeltaY, deltaX, deltaY):

        # returns the point, relative to 0, 0  which extends a distance of "distance"
        # at a slope defined by fDeltaX and fDeltaY

        ptReturn = [0, 0]
        fSlope = 123.  # '''debug remove

        if (fDeltaX == 0):
            ptReturn[0] = deltaX
            ptReturn[1] = math.copysign(distance, fDeltaY + deltaY)
        elif (fDeltaY == 0):
            ptReturn[0] = math.copysign(distance, fDeltaX + deltaX)
            ptReturn[1] = deltaY
        else:
            fSlope = math.atan2(fDeltaY, fDeltaX)
            ptReturn[0] = distance * math.cos(fSlope) + deltaX
            ptReturn[1] = distance * math.sin(fSlope) + deltaY

        #		inkex.errormsg( 'x in= %f y in= %f slope= %f x out= %f y out= %f delta X= %f delta Y= %f' % ( fDeltaX, fDeltaY, fSlope, ptReturn[0], ptReturn[1], deltaX, deltaY ) )
        return ptReturn

Save_file_path = ""
def file_save():
    root.file = asksaveasfile(mode='a')
    global Save_file_path
    Save_file_path = str(root.file)

SVG_open_path = ""
def openSVG():
    # *** open file ***
    root.SVGfile = filedialog.askopenfilename(initialdir="SVGS/", title="Select file", filetypes=(
    ("SVG files", "*.svg"), ("all files", "*.*")))
    global SVG_open_path
    SVG_open_path =str(root.SVGfile)




def close_window():
    root.destroy()

def Fill_path():

    print()
    if (SVG_open_path != "") and (Save_file_path !=""):
        inkex.pathes(str(root.SVGfile),str(root.file.name))
        e = Eggbot_Hatch()
        e.affect()
        if(root.Preview_image.get() =="1"):
            svg_view.svg_file_name(str(root.file.name))
            svg_view.run()

    elif (SVG_open_path == "") and (Save_file_path ==""):
        messagebox.showinfo(title=None, message="Please select a SVG to process and a file to save to")

    elif (SVG_open_path != "") and (Save_file_path == ""):
        messagebox.showinfo(title=None, message="Plese select a file to save to..")

    elif(SVG_open_path == "") and (Save_file_path != ""):
        messagebox.showinfo(title=None, message="Please select a SVG to process.. ")

def filepahts():
   print("svg")

subMenu = Menu(menu)
menu.add_cascade(label="File", menu=subMenu)
subMenu.add_command(label="open SVG", command=openSVG)
subMenu.add_command(label="Save", command=file_save)
subMenu.add_separator()
subMenu.add_command(label="exit", command=close_window)


Label(root, text="This is a stand alone utility using the EGG bot hatch fill utility. ", anchor="w", bg="gray20", fg="lime green").place(x=20, y=20, height=20, width=425)
Label(root, text="Hatch spacing(px)", anchor="w", bg="gray20", fg="lime green").place(x=30, y=45, height=20, width=225)
Label(root, text="Hatch angle (degrees)", anchor="w", bg="gray20", fg="lime green").place(x=30, y=85, height=20, width=225)
Label(root, text="End connections (defaut:3)", anchor="w", bg="gray20", fg="lime green").place(x=30, y=165, height=20, width=225)
Label(root, text="Stroke Width (default:1)", anchor="w", bg="gray20", fg="lime green").place(x=30, y=270, height=20, width=225)
Label(root, text="Tolerance (default:3.0)", anchor="w", bg="gray20", fg="lime green").place(x=30, y=210, height=20, width=225)
Label(root, text="New_page_Width", anchor="w", bg="gray20", fg="lime green").place(x=30, y=325, height=20, width=200)
Label(root, text="New_page_Height", anchor="w", bg="gray20", fg="lime green").place(x=30, y=350, height=20, width=200)
Label(root, text="Stroke Color HEX", anchor="w", bg="gray20", fg="lime green").place(x=30, y=300, height=20, width=200)
# *** check button***
root.Crosshatch = StringVar()
Crosshatch_checkbox = Checkbutton(root, text="Crosshatch?", variable=root.Crosshatch, bg="gray20", fg="lime green",
                 highlightbackground="gray20", activebackground="deep sky blue")
Crosshatch_checkbox.deselect()
Crosshatch_checkbox.place (x=10, y=110)

# *** check button***
root.Ends = StringVar()
Ends_checkbox = Checkbutton(root, text="Connect nearby ends?", variable=root.Ends, bg="gray20", fg="lime green", highlightbackground="gray20",
                 activebackground="deep sky blue")
Ends_checkbox.deselect()
Ends_checkbox.place(x=10, y=130)
'''
# *** check button***
root.Fill_Edge = StringVar()
Fill_edge_checkbox = Checkbutton(root, text="Instert fill from edge", variable=root.Fill_Edge , font=('Helvetica', '12'), bg="gray20",
                 fg="lime green", highlightbackground="gray20", activebackground="deep sky blue")
Fill_edge_checkbox.deselect()
Fill_edge_checkbox.place(x=10,y = 195)
'''

# *** check button***
root.Preview_image = StringVar()
Preview_image_checkbox = Checkbutton(root, text="Preview", variable=root.Preview_image , font=('Helvetica', '12'), bg="gray20",
                 fg="lime green", highlightbackground="gray20", activebackground="deep sky blue")
Preview_image_checkbox.deselect()
Preview_image_checkbox.place(x=10,y = 380)

Button(root, text='Vector Fill', command=Fill_path, bg="gray20", fg="lime green", highlightbackground="gray20",
       activebackground="deep sky blue").place(x=290, y=380, height=25, width=140)
root.configure(background='gray20')

Hatch_spacing = StringVar(root, value='3')
Entry_box_1 = Entry(root, textvariable=Hatch_spacing)

Angle = StringVar(root, value='90.0')
Entry_box_2 = Entry(root, textvariable=Angle)

Range_end = StringVar(root, value='6')
Entry_box_3 = Entry(root, textvariable=Range_end)

Inset_distance = StringVar(root, value='1')
Entry_box_4 = Entry(root, textvariable=Inset_distance)

Tolerance = StringVar(root, value='20.0')
Entry_box_5 = Entry(root, textvariable=Tolerance)

New_page_height = StringVar(root, value='800')
Entry_box_6 = Entry(root, textvariable=New_page_height)

New_page_width = StringVar(root, value='1000')
Entry_box_7 = Entry(root, textvariable=New_page_width)

New_page_width = StringVar(root, value='#FF00FF')
Entry_box_8 = Entry(root, textvariable=New_page_width)

Entry_box_1.place(x=375, y=45, height=20, width=50)
Entry_box_2.place(x=375, y=85, height=20, width=50)
Entry_box_3.place(x=375, y=165, height=20, width=50)
Entry_box_4.place(x=375, y=270, height=20, width=50)
Entry_box_5.place(x=375, y=210, height=20, width=50)
Entry_box_6.place(x=375, y=325, height=20, width=50)
Entry_box_7.place(x=375, y=350, height=20, width=50)
Entry_box_8.place(x=360, y=300, height=20, width=65)

def Hatch_Spacing_px(px_space):
    Entry_box_1.delete(0, END)
    Entry_box_1.insert(0,px_space)
Hatch_Spacing_px(3)
root.Slider_hatch_spacing = DoubleVar()
root.Slider_hatch_spacing.set(3)
root.Hatch_spacing_slider_Val= Scale(root, from_=1, to=25, resolution=.1,length=100,width=7,font=('Helvetica', '8'), orient=HORIZONTAL, bg="gray20",
                           fg="lime green",command=Hatch_Spacing_px,variable=root.Slider_hatch_spacing,
                           highlightbackground="gray20", activebackground="deep sky blue", troughcolor="spring green")
root.Hatch_spacing_slider_Val.place(x=265, y=40)

def Hatch_Angle_Degrees(Hatch_degrees):
    Entry_box_2.delete(0, END)
    Entry_box_2.insert(0,Hatch_degrees)
Hatch_Angle_Degrees(90.0)
root.Slider_Hatch_Angle_Degrees = DoubleVar()
root.Slider_Hatch_Angle_Degrees.set(90.0)
root.Angle_slider_Val= Scale(root, from_=0, to=360, resolution=1,length=100,width=7,font=('Helvetica', '8'), orient=HORIZONTAL, bg="gray20",
                           fg="lime green",command=Hatch_Angle_Degrees,variable=root.Slider_Hatch_Angle_Degrees,
                           highlightbackground="gray20", activebackground="deep sky blue", troughcolor="spring green")
root.Angle_slider_Val.place(x=265, y=80)

def Range_of_End(Range_End_px):
    Entry_box_3.delete(0, END)
    Entry_box_3.insert(0,Range_End_px)
Range_of_End(3.0)
root.Slider_Range_End_px = DoubleVar()
root.Slider_Range_End_px.set(3.0)
root.Range_of_End_slider_Val= Scale(root, from_=0, to=1000, resolution=.1,length=100,width=7,font=('Helvetica', '8'), orient=HORIZONTAL, bg="gray20",
                           fg="lime green",command=Range_of_End,variable=root.Slider_Range_End_px,
                           highlightbackground="gray20", activebackground="deep sky blue", troughcolor="spring green")
root.Range_of_End_slider_Val.place(x=265, y=160)

def Stroke_Distance(Inset_Distance_px):
    Entry_box_4.delete(0, END)
    Entry_box_4.insert(0,Inset_Distance_px)
Stroke_Distance(1.0)
root.Slider_Stroke_px = DoubleVar()
root.Slider_Stroke_px.set(1.0)
root.Stroke_slider_Val= Scale(root, from_=0, to=10, resolution=.2,length=100,width=7,font=('Helvetica', '8'), orient=HORIZONTAL, bg="gray20",
                           fg="lime green",command=Stroke_Distance,variable=root.Slider_Stroke_px,
                           highlightbackground="gray20", activebackground="deep sky blue", troughcolor="spring green")
root.Stroke_slider_Val.place(x=265, y=265)

def Hatch_Tolerance(Hatch_Tolerance_px):
    Entry_box_5.delete(0, END)
    Entry_box_5.insert(0,Hatch_Tolerance_px)
Hatch_Tolerance(3.0)
root.Slider_Hatch_Tolerance_px = DoubleVar()
root.Slider_Hatch_Tolerance_px.set(3.0)
root.Hatch_Tolerance_slider_Val= Scale(root, from_=.1, to=100, resolution=.1,length=100,width=7,font=('Helvetica', '8'), orient=HORIZONTAL, bg="gray20",
                           fg="lime green",command=Hatch_Tolerance,variable=root.Slider_Hatch_Tolerance_px,
                           highlightbackground="gray20", activebackground="deep sky blue", troughcolor="spring green")
root.Hatch_Tolerance_slider_Val.place(x=265, y=205)

root.mainloop()



