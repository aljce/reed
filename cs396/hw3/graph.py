# File: graph.py

"""
This module defines the classes Graph, Node, and Arc, which are used
for working with graphs.  A Graph consists of a set of nodes and a
set of arcs connecting those nodes.  In the graph module, all arcs
are directed; an undirected arc is represented by including an arc
in each direction.

This implementation of the graph package is designed for generality
rather than efficiency.  The package allows arcs connecting a node
to itself and parallel arcs between the same two nodes.

Clients store properties of the nodes and arcs by assigning values
directly to the Node and Arc objects.  The load method makes it easy
to initialize attributes directly from the data file.

The package is designed to facilitate subclassing in which clients
can create their own Node and Arc options.  The Graph class defines
the factory methods createNode and createArc.  Clients can override
these methods to create objects of the appropriate subclass.
"""

import io
import tokenize

class Graph:
    """Defines a graph as a set of nodes and a set of arcs."""

    def __init__(self):
        """Creates an empty graph."""
        self.clear()

    def clear(self):
        """Removes all the nodes and arcs from the graph."""
        self._nodes = { }
        self._arcs = set()

    def addNode(self, arg):
        """
        Adds a node to the graph.  The parameter to addNode is
        either an existing Node object or a string.  If a node is
        specified as a string, addNode looks up that string in the
        dictionary of nodes.  If it exists, the existing node is
        returned; if not, addNode creates a new node with that name.
        The addNode method returns the Node object.
        """
        if type(arg) is str:
            node = self.getNode(arg)
            if node is None:
                node = self.createNode(arg)
        elif isinstance(arg, Node):
            node = arg
        else:
            raise ValueError("Illegal node specification")
        self._nodes[node.getName()] = node
        return node

    def removeNode(self, arg):
        """
        Removes a node from the graph.  The parameter to removeNode is
        either an existing Node object or a string specifying its name.
        Removing a node also removes all arcs into and out of that node.
        Removing a nonexistent node raises a keyError exception.
        """
        if type(arg) is str:
            node = self.getNode(arg)
            if node is None:
                raise ValueError("No node named " + arg)
        elif isinstance(arg, Node):
            node = arg
        else:
            raise ValueError("Illegal node specification")
        for arc in node.getArcsFrom():
            self.removeArc(arc)
        for arc in node.getArcsTo():
            self.removeArc(arc)
        del self._nodes[node.getName()]

    def addArc(self, arg1, arg2=None):
        """
        Adds an arc to the graph.  The parameters to addArc are
        either a single Arc object or a pair of nodes, each of
        which can be an existing Node object or a string.  If a
        node is specified as a string, addArc looks up that name
        in the dictionary of nodes.  If it exists, the existing
        node is returned; if not, addArc creates a new node with
        that name.  The addArc method returns the Arc object.
        """
        if isinstance(arg1, Arc) and arg2 is None:
            arc = arg1
        else:
            start = self.addNode(arg1)
            finish = self.addNode(arg2)
            arc = self.createArc(start, finish)
        self._arcs.add(arc)
        arc.getStart()._addArcFrom(arc)
        arc.getFinish()._addArcTo(arc)
        return arc

    def removeArc(self, arc):
        """
        Removes the specified arc from the graph and from the lists
        internal to each of its endpoint nodes.  This method raises
        a keyError exception if the arc does not exist.
        """
        self._arcs.remove(arc)
        arc.getStart()._removeArcFrom(arc)
        arc.getFinish()._removeArcTo(arc)

    def getNode(self, name):
        """Returns the node with the specified name, or None."""
        return self._nodes.get(name)

    def getNodes(self):
        """Returns a sorted list of all the nodes in the graph."""
        return [ node for node in sorted(self._nodes.values()) ]

    def getArcs(self):
        """Returns a sorted list of all the arcs in the graph."""
        return [ arc for arc in sorted(self._arcs) ]

    def load(self, file):
        """
        Reads graph data from the specified file.  The lines in the file
        take one of two forms: (1) a node specification containing the
        name of the node or (2) an arc specification that includes two
        node names separated either by an operator indicating the type
        of the arc.  The operator -> specifies a directed arc, and the
        operator - specifies an undirected arc, which is implemented as
        one arc in each direction.  Either form may be followed in the
        file by an option string enclosed in parentheses, which is used
        to initialize the attributes of the specific Node or Arc subclass.
        """

        def scanNodeName(token):
            if token.type == tokenize.NAME:
                return token.string
            elif token.type == tokenize.STRING:
                return eval(token.string)
            elif token.type == tokenize.NUMBER:
                return str(eval(token.string))
            else:
                raise SyntaxError("Illegal node name in " + token.line)

        if isinstance(file, str):
            with open(file) as f:
                self.load(f)
        else:
            for line in file:
                line = line.strip()
                if line != "" and not line.startswith("#"):
                    source = io.BytesIO(line.encode("utf-8"))
                    tokenizer = tokenize.tokenize(source.readline)
                    token = next(tokenizer)
                    if token.type == tokenize.ENCODING:
                        token = next(tokenizer)
                    v1 = self.addNode(scanNodeName(token))
                    token = next(tokenizer)
                    op = token.string
                    if op == "-" or op == "->":
                        v2 = self.addNode(scanNodeName(next(tokenizer)))
                        token = next(tokenizer)
                    else:
                        op = None
                    options = None
                    if token.string == "(":
                        p1 = token.end[1]
                        p2 = line.rfind(")")
                        options = line[p1:p2]
                    if op is None:
                        if options is not None:
                            Graph.scanOptions(v1, options)
                    else:
                        arc = self.addArc(v1, v2)
                        if options is not None:
                            Graph.scanOptions(arc, options)
                        if op == "-":
                            arc = self.addArc(v2, v1)
                            if options is not None:
                                Graph.scanOptions(arc, options)

# Implementation notes: Factory methods
# -------------------------------------
# The factory methods createNode and createArc are called to
# create new nodes and arcs.  Clients who want to extend the
# operation of the Graph class do so by defining new subclasses
# for Graph, Node, and Arc and then override these factory
# methods to produce Node and Arc objects of the proper subclass.

    def createNode(self, name):
        """Returns a Node with the specified name."""
        return Node(name)

    def createArc(self, start, finish):
        """Returns a Arc between the specified nodes."""
        return Arc(start, finish)

# Static methods

    @staticmethod
    def scanOptions(obj, options):
        """
        Scans the options string and initializes attributes for obj.
        The general form of the options string is a comma-separated
        list of pairs in the form key=value.  The value may be a
        number, a quoted string, any of several case-independent
        constants (true, false, none, inf), or an identifier taken
        as a string.  For example, the option string

               x=100, y=-2, filled=true, label="my label"

        would set the attribute x to the number 100, y to the number
        -2, filled to the Python Boolean constant True, and label to
        the string "my label".
        """
        source = io.BytesIO(options.encode("utf-8"))
        tokenizer = tokenize.tokenize(source.readline)
        token = next(tokenizer)
        if token.type == tokenize.ENCODING:
            token = next(tokenizer)
        while token.type != tokenize.ENDMARKER:
            if token.type == tokenize.NAME:
                name = token.string
            elif token.type == tokenize.STRING:
                name = eval(token.string)
            else:
                raise SyntaxError("Missing name in option string: " + options)
            token = next(tokenizer)
            if token.string != "=":
                raise SyntaxError("Missing = in option string: " + options)
            token = next(tokenizer)
            sign = 1
            if token.string == "-":
                sign = -1
                token = next(tokenizer)
            if token.type == tokenize.NAME:
                lc = token.string.lower()
                if lc == "false":
                    value = False
                elif lc == "true":
                    value = True
                elif lc == "none":
                    value = None
                elif lc == "inf":
                    value = sign * float("inf")
                else:
                    raise SyntaxError("Illegal option value: " + options)
            elif token.type == tokenize.STRING:
                value = eval(token.string)
            elif token.type == tokenize.NUMBER:
                value = sign * eval(token.string)
            else:
                raise SyntaxError("Illegal option value: " + options)
            setattr(obj, name, value)
            token = next(tokenizer)
            if token.string == ",":
                token = next(tokenizer)

# Overload standard methods

    def __str__(self):
        return self.__repr__()

    def __repr__(self):
        s = ""
        for arc in self.getArcs():
            if len(s) > 0:
                s += ", "
            s += str(arc)
        return "<" + s + ">"

    def __len__(self):
        return len(self._nodes)

# Implementation notes: Node class
# --------------------------------
# The Node class represents a single node in a graph, which is
# identified by a unique name.  Each Node object includes a list
# of the arcs that begin at that node.  The base class for Node
# defines no additional attributes.

class Node:

    def __init__(self, name):
        """Creates a node with the specified name."""
        self._name = name
        self._arcsFrom = set()
        self._arcsTo = set()

    def getName(self):
        """Returns the name of this node."""
        return self._name

    def getArcs(self):
        """Equivalent to getArcsFrom."""
        return self.getArcsFrom()

    def getArcsFrom(self):
        """Returns a list of all the arcs leaving this node."""
        return [ arc for arc in sorted(self._arcsFrom) ]

    def getArcsTo(self):
        """Returns a list of all the arcs ending at this node."""
        return [ arc for arc in sorted(self._arcsTo) ]

    def getNeighbors(self):
        """Returns a list of all the nodes to which at least one arc exists."""
        targets = set()
        for arc in self._arcsFrom:
            targets.add(arc.getFinish())
        return [ node for node in sorted(targets) ]

    def isConnectedTo(self, node):
        """Returns True if any arcs connect to node."""
        for arc in self._arcsFrom:
            if arc.getFinish() is node:
                return True
        return False

# Package methods called only by the Graph class

    def _addArcFrom(self, arc):
        """Adds an arc that starts at this node."""
        if arc.getStart() is not self:
            raise ValueError("Arc must start at the specified node")
        self._arcsFrom.add(arc)

    def _addArcTo(self, arc):
        """Adds an arc that finishes at this node."""
        if arc.getFinish() is not self:
            raise ValueError("Arc must end at the specified node")
        self._arcsTo.add(arc)

    def _removeArcFrom(self, arc):
        """Removes an arc that starts at this node."""
        if arc.getStart() is not self:
            raise ValueError("Arc must start at the specified node")
        self._arcsFrom.remove(arc)

    def _removeArcTo(self, arc):
        """Removes an arc that finishes at this node."""
        if arc.getFinish() is not self:
            raise ValueError("Arc must end at the specified node")
        self._arcsTo.remove(arc)

# Overload standard methods

    def __str__(self):
        return self._name

    def __repr__(self):
        s = self._name
        attributes = ""
        for name,value in vars(self).items():
            if not name.startswith("_"):
                if len(attributes) > 0:
                    attributes += ","
                attributes += name + "=" + repr(value)
        if len(attributes) > 0:
            s += " (" + attributes + ")"
        return s

# Implementation notes: Comparison operators
# ------------------------------------------
# The Node class defines the __lt__ and __le__ comparison
# functions so that nodes can be sorted.  The __gt__ and __ge__
# functions are defined implicitly because Python will
# automatically flip the order.  The comparison is based on the
# names of the nodes, which must be unique within a graph.

    def __lt__(self, other):
        if not isinstance(other, Node):
            return NotImplemented
        elif self is other:
            return False
        elif self._name < other._name:
            return True
        elif self._name > other._name:
            return False
        else:
            raise KeyError("Duplicate names in a graph")

    def __le__(self, other):
        return self is other or self < other

# Implementation notes: Arc class
# -------------------------------
# The Arc class represents a directed arc from one node to another.
# Clients can add attributes to an arc either by direct assignment
# or by creating a subclass with the appropriate getters and setters.

class Arc:
    """This class defines a directed arc from one node to another."""

    def __init__(self, start, finish):
        """Creates an arc from start to finish."""
        self._start = start
        self._finish = finish

    def getStart(self):
        """Returns the node at the start of the arc."""
        return self._start

    def getFinish(self):
        """Returns the node at the end of the arc."""
        return self._finish

# Overload standard methods

    def __str__(self):
        return self._start.getName() + " -> " + self._finish.getName()

    def __repr__(self):
        s = self.__str__()
        attributes = ""
        for name,value in vars(self).items():
            if not name.startswith("_"):
                if len(attributes) > 0:
                    attributes += ","
                attributes += name + "=" + repr(value)
        if len(attributes) > 0:
            s += " (" + attributes + ")"
        return s

# Implementation notes: Comparison operators
# ------------------------------------------
# The Arc class defines the __lt__ and __le__ comparison functions so
# that arcs can be sorted.  The __gt__ and __ge__ functions are defined
# implicitly because Python will automatically flip the order.  The
# comparison first compares the start nodes using the Node comparison
# order.  If the start nodes match, the comparison compares the finish
# nodes.  If those match as well, as they do in parallel arcs between
# the same pair of nodes, the comparison is based on the object id.

    def __lt__(self, other):
        if not isinstance(other, Arc):
            return NotImplemented
        elif self is other:
            return False
        elif self._start < other._start:
            return True
        elif self._start > other._start:
            return False
        elif self._finish < other._finish:
            return True
        elif self._finish > other._finish:
            return False
        else:
            return id(self) < id(other)

    def __le__(self, other):
        return self is other or self < other
