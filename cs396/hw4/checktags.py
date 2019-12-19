# File: CheckTags.py

"""
This program checks that tags are properly matched in an HTML file.
This version of the program runs in Python; the checktags version runs
directly from the command line.
"""

import html.parser
import urllib.request

def CheckTags():
    """Reads a URL from the user and then checks it for tag matching."""
    url = input("URL: ")
    checkURL(url)

def checkURL(url):
    """Checks whether the tags are balanced in the specified URL."""
    try:
        response = urllib.request.urlopen(url)
        parser = HTMLTagParser(url)
        parser.checkTags(response.read().decode("UTF-8"))
    except urllib.error.URLError as e:
        print("URL: " + url + " could not be retrieved because: " + str(e))
    except UnicodeDecodeError as e:
        print("URL: " + url + " is not utf8 encoded")


class HTMLTagParser(html.parser.HTMLParser):

    """
    This class extends the standard HTML parser and overrides the
    callback methods used for start and end tags.
    """

    def __init__(self, base):
        """Creates a new HTMLTagParser object."""
        html.parser.HTMLParser.__init__(self)
        self.base = base

    def checkTags(self, text):
        """Checks that the tags are balanced in the supplied text."""
        self._stack = [ ]
        self.feed(text)
        while len(self._stack) > 0:
            startTag,startLine = self._stack.pop()
            print("Missing </" + startTag + "> for <" + startTag +
                  "> at line " + str(startLine))

    def absolutePath(self, url):
        if "://" in url:
            return url
        else:
            return self.base + url

    def handle_starttag(self, startTag, attributes):
        """Overrides the callback function for start tags."""

        def hasURL(tag, attr):
            href = (tag == "a"   or tag == "link") and attr == "href"
            src  = (tag == "img" or tag == "src" ) and attr == "src"
            return href or src

        startLine,_ = self.getpos()
        self._stack.append((startTag, startLine))
        for attr, url in attributes:
            if hasURL(startTag, attr):
                try:
                    if "mailto" in url:
                        continue
                    fullUrl = self.absolutePath(url)
                    urllib.request.urlopen(fullUrl)
                except urllib.error.URLError as e:
                    endLine,_ = self.getpos()
                    print("Broken link " + fullUrl)
                    print("in <" + startTag + "> at line " + str(endLine))

    def handle_endtag(self, endTag):
        """Overrides the callback function for end tags."""
        endLine,_ = self.getpos()
        if len(self._stack) == 0:
            print("No <" + endTag + "> for </" + endTag +
                  "> at line " + str(endLine))
        else:
            while len(self._stack) > 0:
                startTag,startLine = self._stack.pop()
                if startTag == endTag:
                    break;
                print("Missing </" + startTag + "> for <" + startTag +
                      "> at line " + str(startLine))

# Startup code

if __name__ == "__main__":
    CheckTags()
