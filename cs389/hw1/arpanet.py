# File: arpanet.py

"""
This module defines the classes that are used to represent the graph
structure for the ARPANET.
"""

from pgl import GCompound, GLabel, GLine, GOval, GRect

# Class: ArpanetGraph

class ArpanetGraph:

    """
    This class represents the graph of a network like the ARPANET.
    """

    def __init__(self, gw=None):
        """
        Creates an empty ArpanetGraph, which will be displayed on the
        graphics window passed as the parameter gw.
        """
        self._nodes = { }
        self._gw = gw

    def addNode(self, node):
        """Adds a node to the graph."""
        self._nodes[node.getName()] = node
        return node

    def getNodes(self):
        """Returns a list of the ArpanetNode objects in the graph."""
        return list(self._nodes.values())

    def findNode(self, name):
        """Returns the node with the specified name, or None if not found."""
        return self._nodes.get(name)

    def connect(self, name1, name2):
        """Connects the nodes name1 and name2 with a bidirectional link."""
        n1 = self.findNode(name1);
        if n1 == None:
            raise ValueError("No node named " + name1)
        n2 = self.findNode(name2);
        if n2 == None:
            raise ValueError("No node named " + name2)
        n1.addNeighbor(n2)
        n2.addNeighbor(n1)
        link = GLine(n1.getX(), n1.getY(), n2.getX(), n2.getY());
        if self._gw:
            self._gw.add(link)
            n1.sendToFront()
            n2.sendToFront()
        return link

# Class: ArpanetNode

class ArpanetNode(GCompound):

    """
    This class represents a node in the ARPANET graph.
    """

    SIZE = 8

    def __init__(self, name):
        """Creates a new node with the specified name."""
        GCompound.__init__(self)
        self._name = name
        r = ArpanetNode.SIZE / 2
        oval = GOval(-r, -r, 2 * r, 2 * r)
        oval.setFilled(True)
        self.add(oval)
        self._routingTable = None
        self._active = True
        self._neighbors = set()

    def getName(self):
        """Returns the name of this node."""
        return self._name

    def addNeighbor(self, node):
        """Adds the specified node as a neighbor to this one."""
        self._neighbors.add(node)

    def removeNeighbor(self, node):
        """Removes the specified node from the neighbor set."""
        self._neighbors.remove(node)

    def getNeighbors(self):
        """Returns a list of the neighboring nodes."""
        return list(self._neighbors)

    def setActive(self, flag):
        """Sets whether this node is active, where flag is True or False."""
        self._active = flag

    def isActive(self):
        """Returns True if this node is active."""
        return self._active

    def setRoutingTable(self, table):
        """Sets the routing table for this node."""
        self._routingTable = table

    def getRoutingTable(self):
        """Returns the routing table for this node."""
        return self._routingTable
        
# Class: ArpanetMonitor

class ArpanetMonitor(GCompound):

    """
    This class creates a GCompound that monitors an ArpanetNode and
    displays its routing table.
    """

    WIDTH = 94
    FONT = "12px bold 'Helvetica Neue','Sans-Serif'"
    VSPACE = 13
    MARGIN = 2
    MAX_NODES = 10

    def __init__(self, node):
        GCompound.__init__(self)
        self._node = node
        frame = GRect(ArpanetMonitor.WIDTH,
                      ArpanetMonitor.MAX_NODES * ArpanetMonitor.VSPACE)
        self.add(frame, 0, ArpanetMonitor.VSPACE)
        label = GLabel(node.getName())
        label.setFont(ArpanetMonitor.FONT)
        x = ArpanetMonitor.MARGIN
        y = label.getAscent()
        self.add(label, x, y)
        self._label = label
        self._lines = [ ]
        for i in range(ArpanetMonitor.MAX_NODES):
            y += ArpanetMonitor.VSPACE
            label = GLabel("")
            label.setFont(ArpanetMonitor.FONT)
            self.add(label, x, y)
            self._lines.append(label)
        self.update()

    def update(self):
        node = self._node
        if node.isActive():
            self._label.setColor("Black")
        else:
            self._label.setColor("LightGray")
        table = node.getRoutingTable()
        if table is None:
            return
        names = table.getNodeNames()
        if names is None:
            return
        name = node.getName()
        index = 0
        for i in range(ArpanetMonitor.MAX_NODES):
            self._lines[i].setLabel("")
        for destination in names:
            hopCount = table.getHopCount(destination)
            if hopCount is not None:
                text = destination + ":" + str(hopCount)
                link = table.getBestLink(destination)
                if link is not None and name != link:
                    text += "\u2192" + link
                self._lines[index].setLabel(text)
                index += 1
