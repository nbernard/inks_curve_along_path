#!/usr/bin/env python
# coding=utf-8
#
# Copyright (C) 2022 Nicolas Bernard, nbernard-cappy-b00f7548d@lafraze.net
#               2009 Michel Chatelain
#               2007 Tavmjong Bah, tavmjong@free.fr
#               2006 Georg Wiora, xorx@quarkbox.de
#               2006 Jean-Francois Barraud, barraud@math.univ-lille1.fr
#               2006 Johan Engelen, johan@shouraizou.nl
#               2005 Aaron Spike, aaron@ekips.org
#
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
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
#
# This program is derived from both param_curves.py (itself derived from
# funcplot.py) and from pathalongpath.py
#
"""
This script deforms an object (the pattern) along other paths (skeletons)...
The first selected object is the pattern
the last selected ones are the skeletons.

Imagine a straight horizontal line L in the middle of the bounding box of the pattern.
Consider the normal bundle of L: the collection of all the vertical lines meeting L.
Consider this as the initial state of the plane; in particular, think of the pattern
as painted on these lines.

Now move and bend L to make it fit a skeleton, and see what happens to the normals:
they move and rotate, deforming the pattern.
"""
import sys
import copy
from math import pi, cos, sin, tan, exp

import inkex
from inkex.bezier import pointdistance, beziersplitatt, tpoint, csplength
from inkex.paths import CubicSuperPath

import pathmodifier

def maths_eval(user_function):
    """Try and make the eval safer"""
    func = 'lambda t: ' + (user_function.strip('"') or 't')
    return eval( # pylint: disable=eval-used
        func,
        {
            'pi': pi, 'sin': sin, 'cos': cos, 'tan': tan,
        }, {})

def drawfunction(t_start, t_end, xleft, xright, ybottom, ytop, samples, width, height, left, bottom,
                 fx="cos(3*t)", fy="sin(5*t)", times2pi=False, isoscale=True, drawaxis=True):
    if times2pi:
        t_start *= 2 * pi
        t_end *= 2 * pi

    # coords and scales based on the source rect
    scalex = width / (xright - xleft)
    xoff = left
    coordx = lambda x: (x - xleft) * scalex + xoff  # convert x-value to coordinate
    scaley = height / (ytop - ybottom)
    yoff = bottom
    coordy = lambda y: (ybottom - y) * scaley + yoff  # convert y-value to coordinate

    # Check for isotropic scaling and use smaller of the two scales, correct ranges
    if isoscale:
        if scaley < scalex:
            # compute zero location
            xzero = coordx(0)
            # set scale
            scalex = scaley
            # correct x-offset
            xleft = (left - xzero) / scalex
            xright = (left + width - xzero) / scalex
        else:
            # compute zero location
            yzero = coordy(0)
            # set scale
            scaley = scalex
            # correct x-offset
            ybottom = (yzero - bottom) / scaley
            ytop = (bottom + height - yzero) / scaley

    # functions specified by the user
    f1 = maths_eval(fx)
    f2 = maths_eval(fy)

    # step is increment of t
    step = (t_end - t_start) / (samples - 1)
    third = step / 3.0
    ds = step * 0.001  # Step used in calculating derivatives

    a = []  # path array
    # add axis
    if drawaxis:
        # check for visibility of x-axis
        if ybottom <= 0 <= ytop:
            # xaxis
            a.append(['M', [left, coordy(0)]])
            a.append(['l', [width, 0]])
        # check for visibility of y-axis
        if xleft <= 0 <= xright:
            # xaxis
            a.append(['M', [coordx(0), bottom]])
            a.append(['l', [0, -height]])

    # initialize functions and derivatives for 0;
    # they are carried over from one iteration to the next, to avoid extra function calculations.
    #print("RET: {}".format(f1(1)))
    x0 = f1(t_start)
    y0 = f2(t_start)

    # numerical derivatives, using 0.001*step as the small differential
    t1 = t_start + ds  # Second point AFTER first point (Good for first point)
    x1 = f1(t1)
    y1 = f2(t1)
    dx0 = (x1 - x0) / ds
    dy0 = (y1 - y0) / ds

    # Start curve
    a.append(['M', [coordx(x0), coordy(y0)]])  # initial moveto
    for i in range(int(samples - 1)):
        t1 = (i + 1) * step + t_start
        t2 = t1 - ds  # Second point BEFORE first point (Good for last point)
        x1 = f1(t1)
        x2 = f1(t2)
        y1 = f2(t1)
        y2 = f2(t2)

        # numerical derivatives
        dx1 = (x1 - x2) / ds
        dy1 = (y1 - y2) / ds

        # create curve
        a.append(['C',
                  [coordx(x0 + (dx0 * third)), coordy(y0 + (dy0 * third)),
                   coordx(x1 - (dx1 * third)), coordy(y1 - (dy1 * third)),
                   coordx(x1), coordy(y1)]
                  ])
        t0 = t1  # Next segment's start is this segments end
        x0 = x1
        y0 = y1
        dx0 = dx1  # Assume the functions are smooth everywhere, so carry over the derivatives too
        dy0 = dy1
    return a



def flipxy(path):
    for pathcomp in path:
        for ctl in pathcomp:
            for pt in ctl:
                tmp = pt[0]
                pt[0] = -pt[1]
                pt[1] = -tmp


def offset(pathcomp, dx, dy):
    for ctl in pathcomp:
        for pt in ctl:
            pt[0] += dx
            pt[1] += dy


def stretch(pathcomp, xscale, yscale, org):
    for ctl in pathcomp:
        for pt in ctl:
            pt[0] = org[0] + (pt[0] - org[0]) * xscale
            pt[1] = org[1] + (pt[1] - org[1]) * yscale


def linearize(p, tolerance=0.001):
    """
    This function receives a component of a 'cubicsuperpath' and returns two things:
    The path subdivided in many straight segments, and an array containing the length of each segment.

    We could work with bezier path as well, but bezier arc lengths are (re)computed for each point
    in the deformed object. For complex paths, this might take a while.
    """
    zero = 0.000001
    i = 0
    d = 0
    lengths = []
    while i < len(p) - 1:
        box = pointdistance(p[i][1], p[i][2])
        box += pointdistance(p[i][2], p[i + 1][0])
        box += pointdistance(p[i + 1][0], p[i + 1][1])
        chord = pointdistance(p[i][1], p[i + 1][1])
        if (box - chord) > tolerance:
            b1, b2 = beziersplitatt([p[i][1], p[i][2], p[i + 1][0], p[i + 1][1]], 0.5)
            p[i][2][0], p[i][2][1] = b1[1]
            p[i + 1][0][0], p[i + 1][0][1] = b2[2]
            p.insert(i + 1, [[b1[2][0], b1[2][1]], [b1[3][0], b1[3][1]], [b2[1][0], b2[1][1]]])
        else:
            d = (box + chord) / 2
            lengths.append(d)
            i += 1
    new = [p[i][1] for i in range(0, len(p) - 1) if lengths[i] > zero]
    new.append(p[-1][1])
    lengths = [l for l in lengths if l > zero]
    return new, lengths

def Draw_Linear(drawing, rectangle):
    assert(isinstance(rectangle, inkex.Rectangle))
    # create new path with basic dimensions of selected rectangle
    newpath = inkex.PathElement()
    x = float(rectangle.get('x'))
    y = float(rectangle.get('y'))
    width = float(rectangle.get('width'))
    height = float(rectangle.get('height'))

    # copy attributes of rect
    newpath.style = rectangle.style
    newpath.transform = rectangle.transform

    # top and bottom were exchanged
    newpath.path = \
        drawfunction(drawing.options.t_start,
                     drawing.options.t_end,
                     drawing.options.xleft,
                     drawing.options.xright,
                     drawing.options.ybottom,
                     drawing.options.ytop,
                     drawing.options.samples,
                     width, height, x, y + height,
                     drawing.options.fofx,
                     drawing.options.fofy,
                     drawing.options.times2pi,
                     drawing.options.isoscale,
                     drawing.options.drawaxis)
    newpath.set('title', drawing.options.fofx + " " + drawing.options.fofy)

    # newpath.set('desc', '!func;' + drawing.options.fofx + ';' + drawing.options.fofy + ';'
    #                                      + `drawing.options.t_start` + ';'
    #                                      + `drawing.options.t_end` + ';'
    #                                      + `drawing.options.samples`)

    return newpath

class CurveAlongPath(pathmodifier.PathModifier):
    """Deform a path along a second path"""
    def add_arguments(self, pars):
        pars.add_argument("-n", "--noffset", type=float, default=0.0, help="normal offset")
        pars.add_argument("-t", "--toffset", type=float, default=0.0, help="tangential offset")
        pars.add_argument("-d", "--duplicate", type=inkex.Boolean, default=False,
                          help="duplicate pattern before deformation")
        pars.add_argument("--tab", default="sampling",
                          help="The selected UI-tab when OK was pressed")
        pars.add_argument("--t_start", type=float, default=0.0, help="Start t-value")
        pars.add_argument("--t_end", type=float, default=1.0, help="End t-value")
        pars.add_argument("--times2pi", type=inkex.Boolean, default=True,
                          help="Multiply t-range by 2*pi")
        pars.add_argument("--xleft", type=float, default=-1.0, help="x-value of left")
        pars.add_argument("--xright", type=float, default=1.0, help="x-value of right")
        pars.add_argument("--ybottom", type=float, default=-1.0, help="y-value of bottom")
        pars.add_argument("--ytop", type=float, default=1.0, help="y-value of top")
        pars.add_argument("-s", "--samples", type=int, default=8, help="Samples")
        pars.add_argument("--fofx", default="cos(3*t)", help="fx(t) for plotting")
        pars.add_argument("--fofy", default="sin(5*t)", help="fy(t) for plotting")
        pars.add_argument("--isoscale", type=inkex.Boolean, default=True, help="Isotropic scaling")
        pars.add_argument("--drawaxis", type=inkex.Boolean, default=True)

    def prepare_selection(self):
        """
        first selected->pattern, all but first selected-> skeletons
        """
        skeletons = self.svg.selection.paint_order()

        elem = skeletons.pop()
        if self.options.duplicate:
            elem = elem.duplicate()
        pattern = elem.to_path_element()
        elem.replace_with(pattern)

        self.expand_clones(skeletons, True, False)
        self.objects_to_paths(skeletons)
        return pattern, skeletons.id_dict()

    def lengthtotime(self, l):
        """
        Receives an arc length l, and returns the index of the segment in self.skelcomp
        containing the corresponding point, to gether with the position of the point on this segment.

        If the deformer is closed, do computations modulo the toal length.
        """
        if self.skelcompIsClosed:
            l = l % sum(self.lengths)
        if l <= 0:
            return 0, l / self.lengths[0]
        i = 0
        while (i < len(self.lengths)) and (self.lengths[i] <= l):
            l -= self.lengths[i]
            i += 1
        t = l / self.lengths[min(i, len(self.lengths) - 1)]
        return i, t

    def apply_diffeomorphism(self, bpt, vects=()):
        """
        The kernel of this stuff:
        bpt is a base point and for v in vectors, v'=v-p is a tangent vector at bpt.
        """
        s = bpt[0] - self.skelcomp[0][0]
        i, t = self.lengthtotime(s)
        if i == len(self.skelcomp) - 1:
            x, y = tpoint(self.skelcomp[i - 1], self.skelcomp[i], 1 + t)
            dx = (self.skelcomp[i][0] - self.skelcomp[i - 1][0]) / self.lengths[-1]
            dy = (self.skelcomp[i][1] - self.skelcomp[i - 1][1]) / self.lengths[-1]
        else:
            x, y = tpoint(self.skelcomp[i], self.skelcomp[i + 1], t)
            dx = (self.skelcomp[i + 1][0] - self.skelcomp[i][0]) / self.lengths[i]
            dy = (self.skelcomp[i + 1][1] - self.skelcomp[i][1]) / self.lengths[i]

        vx = 0
        vy = bpt[1] - self.skelcomp[0][1]
        bpt[0] = x + vx * dx - vy * dy
        bpt[1] = y + vx * dy + vy * dx

        for v in vects:
            vx = v[0] - self.skelcomp[0][0] - s
            vy = v[1] - self.skelcomp[0][1]
            v[0] = x + vx * dx - vy * dy
            v[1] = y + vx * dy + vy * dx




    def effect(self):
        path = self.svg.selected[0]
        if len(self.options.ids) != 1: # todo, we should check that path is actually a path
            raise inkex.AbortExtension("This extension requires exactly one selected path.")

        sp = path.path.transform(path.composed_transform()).to_superpath()
        inkex.utils.debug(sp)
        foo,plen = csplength(sp)
        inkex.utils.debug(plen)

        # make rectangle of len plen
        rect = inkex.Rectangle()
        rect.set('x', 0)
        rect.set('y', 0)
        rect.set('height', 20)
        rect.set('width', plen)
        rect.set('style', "fill:none;stroke:#0000FF;stroke-width:0.1")

        #self.svg.add(rect)

        # draw the curve in the rectangle
        curvepath = Draw_Linear(self, rect)
        curvepath.set('style', "fill:none;stroke:#000000;stroke-width:0.1")
        self.svg.add(curvepath)

        inkex.utils.debug(curvepath)
        inkex.utils.debug(type(curvepath))
        inkex.utils.debug(isinstance(curvepath, inkex.PathElement))

        #return
        # todo: pass the curve-path to what follows.
        # pattern = path
        # skels = {"foo": curvepath}
        pattern = curvepath
        skels = {'foo': path}


#        pattern, skels = self.prepare_selection()
        bbox = pattern.bounding_box()

        width = bbox.width
        delta_x = width
        if delta_x < 0.01:
            raise inkex.AbortExtension("The total length of the pattern is too small\n"\
                "Please choose a larger object or set 'Space between copies' > 0")

        if isinstance(pattern, inkex.PathElement):
            pattern.path = self._sekl_call(skels, pattern.path.to_superpath(), delta_x, bbox)

    def _sekl_call(self, skeletons, p0, dx, bbox):
        newp = []
        for skelnode in skeletons.values():
            self.curSekeleton = skelnode.path.to_superpath()
            for comp in self.curSekeleton:
                path = copy.deepcopy(p0)
                self.skelcomp, self.lengths = linearize(comp)
                # !!!!>----> TODO: really test if path is closed! end point==start point is not enough!
                self.skelcompIsClosed = (self.skelcomp[0] == self.skelcomp[-1])

                length = sum(self.lengths)
                xoffset = self.skelcomp[0][0] - bbox.x.minimum + self.options.toffset
                yoffset = self.skelcomp[0][1] - bbox.y.center - self.options.noffset

                for sub in path:
                    offset(sub, xoffset, yoffset)

                for sub in path:
                    for ctlpt in sub:
                        self.apply_diffeomorphism(ctlpt[1], (ctlpt[0], ctlpt[2]))

                newp += path
        return CubicSuperPath(newp)


if __name__ == '__main__':
    CurveAlongPath().run()
