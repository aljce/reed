# File: ArpanetSimulation.py

"""
This file creates a graphical simulation of the early ARPANET.
"""

from arpanet import ArpanetGraph, ArpanetNode, ArpanetMonitor
from routing import RoutingTable
from pgl import GWindow, GLabel, GLine

# Constants

GWINDOW_WIDTH = 1024
GWINDOW_HEIGHT = 550
ALL_BUTTON_X = 30
ALL_BUTTON_Y = 60
ALL_BUTTON_FONT = "14px bold 'Helvetica Neue','Sans-Serif'"
LABEL_FONT = "12px bold 'Helvetica Neue','Sans-Serif'"
MONITOR_SEP = 8
MONITOR_Y = 400

# Node table
# ----------
# The nodes in the network are stored in a constant list, each of whose
# elements is a tuple containing the following values:
#
# - The node name
# - The x coordinate of the center of the dot
# - The y coordinate of the center of the dot
# - The x offset to the start of the node label
# - The y offset to the start of the node label

NODE_TABLE = [
    ("SRI", 120, 134, -27, 5),
    ("STAN", 102, 176, -40, 5),
    ("UCLA", 135, 290, -40, 5),
    ("RAND", 192, 344, -41, 5),
    ("UTAH", 390, 155, -19, 17),
    ("CMU", 585, 60, -15, -7),
    ("BBN", 834, 29, 7, 5),
    ("MIT", 861, 68, 7, 5),
    ("HARV", 876, 110, 7, 5),
    ("NRL", 783, 224, 7, 7)
]

# Main program for the simulation

def ArpanetSimulation():
    def clickAction(e):
        nodeList = [ ]
        obj = gw.getElementAt(e.getX(), e.getY())
        if isinstance(obj, ArpanetNode):
            nodeList = [ obj ]
        elif isinstance(obj, GLine):
            active = obj.getColor() == "Black"
            start = obj.getStartPoint()
            end = obj.getEndPoint()
            n1 = gw.getElementAt(start.getX(), start.getY())
            n2 = gw.getElementAt(end.getX(), end.getY())
            if active:
                obj.setColor("LightGray")
                n1.removeNeighbor(n2)
                n2.removeNeighbor(n1)
            else:
                obj.setColor("Black")
                n1.addNeighbor(n2)
                n2.addNeighbor(n1)
        elif obj == allButton:
            nodeList = arpanet.getNodes()
        elif isinstance(obj, GLabel):
            node = arpanet.findNode(obj.getLabel())
            name = node.getName()
            if node.isActive():
                node.setActive(False)
                obj.setColor("LightGray")
                node.setRoutingTable(RoutingTable(name))
                monitors[name].update()
            else:
                node.setActive(True)
                obj.setColor("Black")
                monitors[name].update()
        for node in nodeList:
            name = node.getName()
            myTable = node.getRoutingTable()
            if node.isActive():
                for neighbor in node.getNeighbors():
                    if neighbor.isActive():
                        neighbor.getRoutingTable().update(name, myTable)
        for name in monitors:
            monitors[name].update()

    gw = GWindow(GWINDOW_WIDTH, GWINDOW_HEIGHT)
    arpanet = createArpanetGraph(gw)
    monitors = createArpanetMonitors(gw, arpanet)
    allButton = GLabel("Update All")
    allButton.setFont(ALL_BUTTON_FONT)
    gw.add(allButton, ALL_BUTTON_X, ALL_BUTTON_Y)
    gw.addEventListener("click", clickAction)

def createArpanetGraph(gw):
    graph = ArpanetGraph(gw)
    for name, x, y, dx, dy in NODE_TABLE:
        node = ArpanetNode(name)
        node.setRoutingTable(RoutingTable(name))
        graph.addNode(node)
        gw.add(node, x, y)
        label = GLabel(name)
        label.setFont(LABEL_FONT)
        gw.add(label, x + dx, y + dy)
    graph.connect("BBN", "CMU")
    graph.connect("BBN", "MIT")
    graph.connect("BBN", "UTAH")
    graph.connect("CMU", "NRL")
    graph.connect("CMU", "UTAH")
    graph.connect("HARV", "MIT")
    graph.connect("HARV", "NRL")
    graph.connect("MIT", "HARV")
    graph.connect("NRL", "RAND")
    graph.connect("RAND", "UCLA")
    graph.connect("SRI", "STAN")
    graph.connect("SRI", "UTAH")
    graph.connect("STAN", "UCLA")
    return graph

def createArpanetMonitors(gw, arpanet):
    monitors = { }
    n = len(NODE_TABLE)
    totalWidth = n * ArpanetMonitor.WIDTH + (n - 1) * MONITOR_SEP
    x = (gw.getWidth() - totalWidth) / 2
    for node in arpanet.getNodes():
        monitor = ArpanetMonitor(node)
        monitors[node.getName()] = monitor
        gw.add(monitor, x, MONITOR_Y)
        x += ArpanetMonitor.WIDTH + MONITOR_SEP
    return monitors

# Startup code

if __name__ == "__main__":
    ArpanetSimulation()
