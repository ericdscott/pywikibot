#!/usr/bin/python
# -*- coding: utf-8 -*-
"""Template harvesting script.

This script expands on template_harvest.py by allowing for the specification
of constraints and aggregation policies for values parsed from a given template.

Usage:
(on one line)

python pwb.py constrained_harvest.py  -c:<path/to/spec/file.ttl> -r:<run_name> \
[-blacklist <path/to/blacklist.txt>]?\
[-whitelist <path/to/whitelist.txt>]?\
[-simulate]? \
[other global options]?

Where:

<path/to/spec/file.ttl> is an RDF file (typically ttl) which specifies
one or more harvest runs. See constained_harvest.ttl for the
supporting RDF ontology.

<run_name> is a string which should regex-match the URI of exactly one
Harvest specification in <path/to/spec/file.ttl>.

These options should infer -lang and -template and -family pwb global options

Optional:
<blacklist> Sometimes you run a script for a long time and it hits
  some kind of glitch and the run stops. If you can access the log
  file and extract a set of page titles  to a blacklist file, providing
  that file as a -blacklist option will skip these titles, and you
  can pick up where you left off.
<whitelist> A list of page titles s.t. any non-matching page should be skipped
  typically used for testing purposes
<other global options> : see 
  https://www.mediawiki.org/wiki/Manual:Pywikibot/Global_Options
"""

# (C) Eric D. Scott (WMF acct: lisp.hippie), 2018.
# Derived and adapted from scripts/harvest_template.py
# (C) Multichill, Amir, 2013
# (C) Pywikibot team, 2013-2014
#
# Distributed under the terms of MIT License.
#

# STYLE TODO: Change camelCase function names to under_scored.
# SYTLE TODO: Make string quotation more consistent

from __future__ import absolute_import, unicode_literals

__version__ = '$Id$'
#
import sys
reload(sys)
sys.setdefaultencoding('utf-8')
import os
import re
import signal
import string
import time
import urlparse
from functools import reduce, partial
import httplib
import requests
import json
import pystache
import pdb
import rdflib
from rdflib import util as rdf_util
import pywikibot.data.sparql as sparql
import pywikibot
from pywikibot import pagegenerators as pg, textlib, WikidataBot

willstop = False

#################
# UTILITIES
#################

def _signal_handler(signal,frame):
    global willstop
    if not willstop:
        willstop = True
        print('Received ctrl-c. Finishing current item; '
              'press ctrl-c again to abort.')  # noqa
    else:
        raise KeyboardInterrupt

signal.signal(signal.SIGINT,_signal_handler)

docuReplacements = {'&params;': pywikibot.pagegenerators.parameterHelp}

def getHttpStatus(url,timeout=10):
    """
    Returns (<status or None>, <reason>, <value>)
    Where 
    <reason> and <value> are values if <status is None>
    <timeout> is in seconds
    Note: Typically used to validate URLs parsed from template
    """
    parse = urlparse.urlparse(url)
    try:
        conn = httplib.HTTPConnection(parse.netloc, timeout=timeout)
        conn.request("HEAD", parse.path or "/")
        r = conn.getresponse()
        return [r.status, r.reason, r.read()]
    except Exception as e:
        return [None, str(e), ""]

def merge(dicta, dictb):
    """Returns a new dict merged from <dicta> and <dictb>. 
    Keys in <dictb> will supersede <dicta> on collision.
    """
    result = dicta.copy()
    result.update(dictb)
    return result

def nested_expression(expr):
    """
    Returns (parsed, unparsed)
    Where
    <parsed> is the substring of <expr> that matches nesting from the first 
      char of <expr>
    <unparsed> is the substring of <expr> that follows <parsed>
    NOTE: typically used to parse template info
    """
    expr = expr.strip()
    if expr == "":
        return ("", "")
    # pywikibot.output("expr in ne:%s" % expr)
    nesting_char = expr[0]
    # pywikibot.output("nesting_char:%s" % nesting_char)
    if nesting_char not in ['{', '[', '(']:
        return ("", expr)
    closing_char = {'{' : '}', '[' : ']', '(' : ')'}
    nesting_level = 0
    # search for closing char at same nesting level...
    for i in range(len(expr)):
        c = expr[i]
        if c == closing_char[nesting_char]:
            nesting_level = nesting_level = nesting_level - 1
        if i > 0 and nesting_level == 0:
            return (expr[:i+1], expr[i+1:])
        if c == nesting_char:
            nesting_level = nesting_level + 1
    assert nesting_level == 0

####################
# SPARQL ENDPOINTS
####################

def askQueryWithRetries (query,retry_schedule=[10,60,300]):
    """
    Returns True iff <query> is true. Retries after (by default) 10, 
      60, and 300 seconds, then fails.
    Where
    <query> is a SPARQL ASK query.
    <retry_schedule> := [<pause>, ....]
    <pause> is the number of seconds to wait before the next retry.
    """
    q = sparql.SparqlQuery()

    for retries in retry_schedule:
        try:
            return q.ask(query)
        except requests.exceptions.ConnectionError as e:
            pywikibot.output("Connection Error. Retrying in %s..." 
                             % retries)
            time.sleep (retries)
        except requests.exceptions.Timeout as e:
            pywikibot.output("Timeout. Retrying in %s" 
                             % (retries * 2))
            time.sleep (retries * 2)
        except Exception as e:
            pywikibot.output("this type of error fell through posing "
                             + "SPARQL query:%s" % type(e))
            raise e
    return q.ask(query)

def selectQueryWithRetries (query,retry_schedule=[10,60,300]):
    """
    Returns [<binding>, ...] in response to <query>. Retries after
      (default) 10, 60, and 300 seconds, then fails.
    Where
    <query> is a SELECT SPARQL query.
    <retry_schedule> := [<pause>, ....]
    <pause> is the number of seconds to wait before the next retry.
    """

    q = sparql.SparqlQuery()
    for retries in retry_schedule:
        try:
            return q.select(query)
        except requests.exceptions.ConnectionError as e:
            pywikibot.output("Connection Error. Retrying in %s..." % retries)
            time.sleep (retries)
        except requests.exceptions.Timeout as e:
            pywikibot.output("Timeout. Retrying in %s" % (retries * 2))
            time.sleep (retries * 2)
        except Exception as e:
            pywikibot.output("this type of error fell through in checkRangeConstts:%s" % type(e))
            raise e
    return q.select(query)


#######################
# LITERALS SUPPORT
#######################


def standardLiteralHandlers(pnum):
    """
    Returns (<interpret>, <check>) appropriate for <pnum>
    Where
    <interpret> := fn(maybe_bad_literal) -> [<good literal>, ...]
    <check> := fn(good_literal) -> True iff <good literal> is appropriate for
      <pnum>
    <pnum> is a WD property
    NOTE: add cases to this logic wherever you expect handlers to be 
      generally applicable for all template fields mapped to  some p-number
    """
    strip = lambda s : [s.strip()]

    assume_true = lambda s : True
    
    strip_ref_name = lambda s: [re.sub("<ref name=.*", "", strip(s))]

    def all_caps(s):
        result = re.match("^[A-Z0-9]+$", s)
        return result != None
    
    # TODO: consider moving this to the ontology
    if pnum  == "P229":  # IATA
        def p229_check(s):
            return all_caps(s) and len(s) == 2
        return (strip_ref_name,
                p229_check)

    if pnum == "P230":  # ICAO
        def p230_check(s): 
            return all_caps(s) and len(s) == 3
        return (strip_ref_name,
                p230_check)

    # default...
    return (strip, assume_true)

# QUANTITIES:
# Handles claim.type == 'quantity' parsed from template
def standard_quantity_handlers(pnum):
    """
    Returns (<interpret>, <check>), possibly tailored for 
      specific <pSpec>
    <interpret> := fn(data_string) -> [<quantity>, ...]
    <check> := fn(<quantity>) -> True iff appropriate for pSpec

    NOTE: edit this function for specific parameters for values you 
      expect to apply universally across all bot runs..
    """
    
    def parse_quantities(quantity_string):
        quantity = quantity_string.strip()
        return [pywikibot.WbQuantity(amount=quantity, error=1)]

    def assume_true(quantity):
        return lambda quantity: True

    return (parse_quantities, assume_true)

# URLs #####
# Handles claim.type == 'url' parsed from template
def standard_url_handlers(pnum):
    """
    Returns (<interpret>, <check>) appropriate for <p number>
    Where
    <interpret> := fn(url_string) -> [<proper url>] or [] if
      a URL could not be parsed
    <check> := fn(scheme, hostEtc) -> True iff the resulting URL is valid and 
      suitable for <p number>. Also makes a call against the URL to confirm
      a normal response code.
    """
    
    def interpret(value):
        # Returns fn(ugly url)-> <pretty url>, or None if a URL couldn't be 
        # parsed
        noFrame = value.strip("{}[] ")
        # TODO: use nested_expression() and proper template parsing
        # TODO: consider referencing the ontology for stuff like 'Resmî site'
        match = re.match("(URL\||Resmî site\|)?((http|https)://)?([^ |]+).*", 
                         noFrame, 
                         re.IGNORECASE)
        if match:
                urlTag, scheme, schemeType, hostEtc = match.groups()
                hostEtc = re.sub("//$", "/", hostEtc) # // happens sometimes
                hostEtc = re.sub("[\{\}<>].*$", "", hostEtc) # there were multiple braces
                if not scheme and re.match(".*www.*", hostEtc):
                    scheme = "http://"
                else:
                    return []
                return [scheme + hostEtc]
        return []
    def check_url(url): 
        # returns True iff <url> can be parsed and gets a valid http response
        if not url:
            return False
        try:
            if re.match(".*[\|].*", url):
                pywikibot.output("Weird characters in %s. Skipping" % url)
                return False
            (scheme, host, path, query, fragment) = urlparse.urlsplit(url)
            if not (re.match(".*http|https):", scheme)
                    and '.' in host):
                return False
            [status, reason, data] = getHttpStatus(url)
            if status not in [200, 302, 301]:
                pywikibot.output("No HTTP response for %s. Skipping." % url)
                return False
            return True
        except ValueError as e:
            pywikibot.output(str(e))
            return False

    # put any P-number specific cases here
    # default...
    return (interpret, check_url)

# WIKIBASE ITEMS
# Handles claim.type == 'wikibase-item' parsed from template

def template_link_target(item, link_text):
    """
    Returns: [<linked item>,...] for link(s) parsed from <link_text> 
      or None if <linked item> == <item>
    Where
    <item> := an instance of page.ItemPage dedicated to some Q-number, 
       typically the subject of some claim
    <linked item> matches pywikibot.link_regex, typically of the form 
      [[<wikipedia page>]], or <value> if no translation can be inferred.
    <link text> was parsed from a template, e.g. [[Russia]]
    """
    linked_page = None
    link = pywikibot.Link(link_text.strip())
    linked_page = pywikibot.Page(link)
    # pywikibot.output("linked_page in tlt:%s" % linked_page)
    try:
        if not linked_page.exists():
            pywikibot.output('%s does not exist so it cannot be linked. '
                             'Skipping.' % (linked_page))
            return
    except Exception as e:  
            pywikibot.output(str(e))
            return          

    if linked_page.isRedirectPage():
        pywikibot.output("linked page is redirect page")
        linked_page = linked_page.getRedirectTarget()

    try:
        # pywikibot.output("linked page :%s" % linked_page)
        linked_item = pywikibot.ItemPage.fromPage(linked_page)
    except pywikibot.NoPage:
        linked_item = None
    except Exception as e:
        pywikibot.output(str(e))
        linked_item = None

    if not linked_item or not linked_item.exists():
        pywikibot.output('%s does not have a wikidata item to link with. '
                         'Skipping.' % (linked_page))
        return

    if linked_item.title() == item.title():
        pywikibot.output('%s links to itself. Skipping.' % (linked_page))
        return
    # pywikibot.output("returning tlt %s" % linked_item)
    return linked_item


# TEMPLATE DATA
br_delimiter = re.compile("<br.*?>", re.IGNORECASE)

def parse_template_data (spec, site): 
    """
    Returns [<page spec>, ...]
    Where
    <spec> is a string parsed from a template which may be parsable further 
      for wiki pages.
    <site> := the wikibase API site
    <page spec> should be a suitable argument for pywikibot.Link()
    """
    pywikibot.output("starting parse_template_data for spec %s" % spec)
    spec = spec.replace("\n", " ").strip()
    request = pywikibot.data.api.Request(
        site, 
        parameters={'action': 'parse',
                    'text' : spec,
                    'contentmodel': "wikitext",
                    'format' : "json"
                })
    response= pywikibot.comms.http.request(site, str(request))
    # pywikibot.output("response from api:%s" % response)
    try:
        response = json.loads(response)
    except ValueError as e:
        pywikibot.output(e)
        return []
    def link_order_key(link):
        m = re.search(link, response["parse"]["text"]["*"])
        return m.start()
    get_link = lambda link: link['*']
    links = [get_link(l) for l in response['parse']['links']
             if not re.match("^help:.*", str(l), re.IGNORECASE)]

    # the links have to be sorted in the order they appear in the 
    # template ...
    try:
        links = sorted(links, key=link_order_key)
        pywikibot.output("links:%s" % links)
        # if len(links) > 1:
        #     for link in links:
        #         pywikibot.output("pos of %s: %s" % (link, link_order_key(link)))
        return links
    except Exception as e:
        pywikibot.output(e)
        return []


def standard_wikibase_item_handlers(pnum, repo, site):
    """
    Returns (interpret, check) appropriate typical assignments of wikibase 
      items (Q-numbers) parsed from a template for <pnum>.
    Where
    <interpret> := fn(template_text, item, repo) -> [<item page>, ...]
    <check> := fn(item_page) -> True iff <item page> is well-formed and valid
    <template text> is a string parsed from some template and recognized as 
      claim.type == 'wikibase-item'
    <repo> is a wikibase repository, associated with the orgiginating bot 
      class, typically the value of <bot>.repo in the calling function.
    <item page> is a page in Wikidata associated with some Q-number
    """

    # pywikibot.output("Getting handlers for pnum %s" % pnum)
    def get_item_pages(value,item,repo):
        # pywikibot.output("value:%s/%s" % (value, type(value)))
        if type(value) == pywikibot.page.ItemPage:
            return [value]
        value = unicode(value)
        wikidata_page_spec_re = re.compile ("(Q[0-9]+)", 
                                            re.IGNORECASE)
        def parse_wikidata_page_spec(m):
            q_number = m.group(1)
            return pywikibot.ItemPage(repo, title=q_number)

        def get_item_page(page_spec):
            # returns a single ItemPage for <value>, or None if the value 
            # couldn't be parsed
            pywikibot.output("getting item page for %s" % page_spec)
            #pywikibot.output("about to get template_link_target for %s" 
            #                 % page_spec)
            return template_link_target(item, page_spec)

        m = wikidata_page_spec_re.match(value)
        # pywikibot.output("match to %s:%s" % (value, m))
        if m:
            return [parse_wikidata_page_spec(m)]
        # else not a Q-number...
        return [get_item_page(v) for v 
                # in maybeTranslate(value)]
                in parse_template_data(value, site)]

    not_null = lambda x : not (not (x))
    return (get_item_pages, not_null)

# TIME STUFF ####
# MONTHS ####

def ru_month_genitive_mapping_fn ():
    """
    Returns fn(month_name) -> genitive case mapping for a russian month
    Note: typically used to inform a regex the recognizes month names
    """
    # TODO: consider moving this to the supporting ontology
    # Genitive case mappings...
    table = {"январь" :	"января",
             "февраль" : "февраля",
             "март" :	"марта",
             "апрель" :	"апреля",
             "май" :	"мая",
             "июнь" :	"июня",
             "июль" :	"июля",
             "август" :	"августа",
             "сентябрь" : "сентября",
             "октябрь" :  "октября",
             "ноябрь" :	"ноября",
             "декабрь" : "декабря"
    }
    def genitive_mapping_for(monthName):
        if monthName in table:
            return [monthName, table[monthName]]
        return [monthName]
    return genitive_mapping_for

def month_variants_fn_for(language):
    """
    returns fn(token) -> [<token>, <variant>*]
    Where
    <token> is a month of the year
    <variant> is an optional  morphological variant not expected to be 
      found as WD alias
    Note: so far this is only defined for Russian, all other languages
      simply return [<token>]
    Note: this is typically used to inform a regex that recognizes 
      month names.
    """
    if language == "ru":
        return ru_month_genitive_mapping_fn()
    # add handlers for other languages here if they need special handling

    # default is to assume no mophological variation...
    return lambda x: x 

def acquire_month_name_to_number():
    """
    Returns {<monthName> : <number>, ...}
    Where:
    <monthName> is a down-cased name for the <number>'th month in both 
      English and pywikibot.config.mylang according to Wikidata
    Note: this typically populates the cache that informs 
      month_name_to_number(), and a regex month recognizer
    """
    template = """
        PREFIX wd: <http://www.wikidata.org/entity/>
        PREFIX wdt: <http://www.wikidata.org/prop/direct/>
        PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
        Select ?monthName ?enLabel
        Where
        {
          ?monthQ wdt:P279 wd:Q18602249; # Month of Gregorian
          rdfs:label ?enLabel;
          .
          Filter (Lang(?enLabel) = "en")
          {
            {
              ?monthQ rdfs:label ?monthLabel.
              Filter(Lang(?monthLabel) = "{{Lang}}")
            }
            Union
            {
              ?monthQ skos:altLabel ?monthLabel.
              Filter(Lang(?monthLabel) = "{{Lang}}")
            }
          }
          Bind(Str(?monthLabel) as ?monthName)
        }
        """
    query = pystache.render(template,
                           {"Lang" : pywikibot.config.mylang})
    
    table = {
        "january" : 1,
        "february" : 2,
        "march": 3,
        "april": 4,
        "may": 5,
        "june" : 6,
        "july" : 7,
        "august" : 8,
        "september" : 9,
        "october" : 10,
        "november" : 11,
        "december" : 12
    }
    bindings = selectQueryWithRetries(query)
    
    month_variants_fn = month_variants_fn_for(pywikibot.config.mylang)

    def collect_month_entries(month_entries, binding):
        # month_entries := {<monthName> : <number>, ...}
        for variant in month_variants_fn(binding['monthName'].lower()):
            month_entries[variant] = table[binding['enLabel'].lower()]
        return month_entries
    
    for binding in bindings:
        table = collect_month_entries(table, binding)
    return table
    

_month_name_to_number_cache = None
def monthNameToNumber(monthName):
    """
    Returns 1-12 according to <monthName>, or 0 if not found.
    """
    global _month_name_to_number_cache
    if not _month_name_to_number_cache:
        _month_name_to_number_cache = acquire_month_name_to_number()
    return _month_name_to_number_cache.get(monthName.lower(), 0)

def month_name_recognizer():
    """
    Returns a regex that recognizes month names in English and the 
    current language.
    """
    global _month_name_to_number_cache
    if not _month_name_to_number_cache:
        _month_name_to_number_cache = acquire_month_name_to_number()
    add_boundaries = lambda s:  "^" + s + "$"
    return re.compile('|'.join([add_boundaries(k) 
                                for k 
                                in _month_name_to_number_cache.keys()]),
                      re.IGNORECASE|re.UNICODE)

def parse_timestrings(parsed, timestring):
    """
    Returns <parsed> << [<new_parsed_expression>, ...] , <unparsed>
    Where:
    <parsed> := [<parsed_expression>, ...]
    <unparsed> is a substring of <timestring> which has not yet been parsed.
    """
    # pywikibot.output("timestring in pt:%s" % timestring)
    assert type(parsed) == type([])
    def parse_template(parsed, instring):        
        nested, unparsed = nested_expression(instring)
        if nested:
            nested = nested.strip('{{}}')
            pipe_split = (nested.split('|'))
            template_type = pipe_split[0].lower()
            contents = "|".join(pipe_split[1:])
            pywikibot.output("contents in pt:%s" % contents)
            if template_type in ["nowrap", "nobreak", "no break"]:
                br_split = re.split(br_delimiter, contents)
                pywikibot.output("br_split in pt:%s" % br_split)
                for se in br_split:
                    parsed = parse_timestrings(parsed, se)
            elif template_type in ["plainlist"]:
                def normalize(s):
                    return s.strip()
                bullet_split = [normalize(s)
                                for s in re.split("[*]", 
                                                  contents.replace("\n", " "))
                                if s.strip() != ""]
                for se in bullet_split:
                    parsed = parse_timestrings(parsed, se)
            else:
                #raise Exception("what to do with template type %s?" 
                #                % template_type)
                pywikibot.output("Don't know what to do with template type %s"
                                 % template_type)
                return (parsed, "")
        return (parsed, unparsed)

    def parse_link (parsed, instring):
        nested, unparsed = nested_expression(instring)
        # pywikibot.output("p: %s / u:%s" % (nested, unparsed))
        nested = nested.strip('[[]]')
        split_link = nested.split('|')
        if len(split_link) == 2:
            return (parsed + [split_link[1]], unparsed)
        return (parsed + [split_link[0]], unparsed)

    year_regex = re.compile("^([0-9]{4})([^-].*)")
    def parse_year(parsed, instring):
        m = year_regex.match(instring)
        assert not re.match("^[0-9].*", m.group(2))
        return (parsed + [m.group(1)], m.group(2))

    range_regex = re.compile("^([0-9]{4}[-][0-9]{2,4})(.*)")
    def parse_range(parsed, instring):
        m = range_regex.match(instring)
        return (parsed + [m.group(1)], m.group(2))

    break_regex = re.compile("^(.*?)<br.*?>(.*)", re.IGNORECASE)
    def consume_break(parsed, instring):
        m = break_regex.match(instring)
        content = m.group(1).strip()
        if content == "":
            content = "no_entry"
        remainder = m.group(2).strip()
        return (parse_timestrings(parsed, content), remainder)

    def graft(parsed, instring):
        # aggregates comma- or &- separated values
        last_entry = parsed[-1]
        if type(last_entry) != type([]):
            last_entry = [last_entry]
        separator =  instring[0]
        substrings = instring.split(separator)
        for s in substrings:
            last_entry = parse_timestrings(last_entry, s)
        parsed = parsed[:len(parsed)-1] + [last_entry]
        return (parsed, "")
               
    parsed, unparsed = (parsed, timestring)
    safety = 0
    while unparsed != "":
        unparsed = re.sub("\s*-\s*", '-', unparsed)
        unparsed = unparsed.strip()
        #pywikibot.output("unparsed:%s" % unparsed)
        #pywikibot.output("unparsed[0]:%s" % unparsed[0])
        safety = safety + 1
        assert safety < 20 
        
        if unparsed[0] == '{':
            parsed, unparsed = parse_template(parsed,unparsed)
        elif unparsed[0] == '[':
            parsed, unparsed = parse_link(parsed,unparsed)
        elif (unparsed[0] in [',', '&']) and not (re.match("&.*;", unparsed)):
            #pywikibot.output("about to graft %s" % unparsed)
            parsed, unparsed = graft(parsed, unparsed)
        elif break_regex.match(unparsed):
            parsed, unparsed = consume_break(parsed, unparsed)
        elif range_regex.match(unparsed):
            parsed, unparsed = parse_range(parsed,unparsed)
        elif year_regex.match(unparsed):
            parsed, unparsed = parse_year(parsed, unparsed)
        else:
            #print ("dealing with plain string %s" % unparsed)
            parsed, unparsed = (parsed + [unparsed], "")
    return parsed
    
def parseTimeValue(timestring):
# returns (Y, M, D, H, m, S, prec), parameters for wbTime.
# timestring is whatever was parsed from the template
# def getYMD (tokens):
#     # returns e.g. [2000, 1, 1]
#     # matchGroup := (<YMDStr>) a singleton match group from 
#     # some regex matched to <timestring>
#     [Y, M, D] = tokens
#     def isNumber (s):
#         return re.match("[0-9]+", s)
#     YMD= map(int, list(filter (isNumber, tokens)))
#     pywikibot.output("YMD::%s" % YMD)
#     return YMD

    print ("Parsing time value %s" % timestring)
    def getMonthNameDY (tokens):
        # returns [Y, M, D] from matchGroups like (January, 1, 2000)
        [monthName, D, Y] = tokens
        M = monthNameToNumber(monthName)
        if M == 0:
            return [0, 0, 0]
        YMD = map(int, [Y, M, D])
        pywikibot.output("YMD in gmndy::%s" % YMD)
        return YMD

    def getMonthNameY (tokens):
        # returns [Y, M, D] from matchGroups like (January 2000)
        [monthName, Y] = tokens
        M = monthNameToNumber(monthName)
        if M == 0:
            return [0, 0]
        YM = map(int, [Y, M])
        pywikibot.output("YM in gmndy::%s" % YM)
        return YM

    def getDMonthNameY (tokens):
        # returns [Y, M, D] from matchGroups like (1 January, 2000)
        [D, monthName, Y] = tokens
        M = monthNameToNumber(monthName)
        if M == 0:
            return [0, 0, 0]
        YMD = map(int, [Y, M, D])
        pywikibot.output("YMD in gdmny::%s" % YMD)
        return YMD

    def getY (tokens):
        # returns [Y, M, D] from matchGroups like (2000)
        [yearStr] = tokens
        Y = [int(yearStr)]
        # pywikibot.output("Year in gdmny::%s" % Y)
        return Y

    neither_number_nor_word =re.compile("[^\w\d]+", re.UNICODE)
    is_month_name = month_name_recognizer()

    def simplify(timestring):
        # returns (<pattern>, <date tokens>)
        timestring = re.sub(neither_number_nor_word, " ", timestring)
        print("timestring after sub:%s" % timestring)
        tokens = timestring.split(' ')
        print("timestring tokens:%s" % tokens)
        def collect_date_tokens(valence_pattern_tokens, token):
            # <pattern_tokens> << (<pattern>, [<token>, ...])
            # where each character in <pattern> classifies
            # the corresponding <token> of <timestring>
            # as M = month name, N = number, X =  other
            # the pattern will be matched downstream for 
            # appropriate handling
            # pywikibot.output("token:%s" % token)
            valence, pattern, tokens = valence_pattern_tokens
            if re.match("^BC[E]?$", token):
                return ("-", pattern, tokens)
            if re.match("^[\d]+$", token):
                return (valence, pattern + "N", tokens + [token])
            if is_month_name.match(token):
                return (valence, pattern + "M", tokens + [token])
            return (valence, pattern + "X", tokens)
        return reduce(collect_date_tokens, tokens, ("+", "", []))

    valence, pattern, date_tokens = simplify(timestring)
    pywikibot.output("simplified:%s/%s/%s" % (valence, pattern, date_tokens))

    if re.match("^X*MNNX*$", pattern):
        [Y, M, D] = getMonthNameDY(date_tokens)
        return (valence, Y, M, D, 0, 0, 0, 11)

    if re.match("^X*NMNX*$", pattern):
        [Y, M, D] = getDMonthNameY(date_tokens)
        return (valence, Y, M, D, 0, 0, 0, 11)

    if re.match("^X*MNX*$", pattern):
        [Y, M] = getMonthNameY(date_tokens)
        return (valence, Y, M, 0, 0, 0, 0, 11)

    if re.match("^X*NNNX*$", pattern):
        # can't really tell if its D/M/Y or M/D/Y. skip
        pywikibot.output("Can't tell if %s is D/M/Y or M/D/Y. "
                         % timestring
                         + "Skipping")
        return ("", 0, 0, 0, 0, 0, 0, 0)

    if re.match("^X*NX*$", pattern):
        [Y] = getY(date_tokens)
        return (valence, Y, 0, 0, 0, 0, 0, 9)

    pywikibot.output("Fell through parsing timestring '%s'. "
                     % timestring
                     + "Skipping.")
    return ("", 0, 0, 0, 0, 0, 0, 0)


def create_time_spec(timestring):
    """
    Returns {?at} or {?from ?to}  as appropriate to <timestring>
    Where:
    <at>, <from>, <to> are all instances of WbTime
    """
    def make_WbTime(spec):
        (valence, Y, M, D, H, m, S, prec) = spec
        if valence == "-":
            Y = Y * -1
        return pywikibot.WbTime(year = Y, 
                                month = M, 
                                day = D, 
                                hour = H, 
                                minute = m, 
                                second = S,
                                precision = prec)

    print ("timestring in cts:%s" % timestring)
    range_split = timestring.split('-')
    print("range split:%s" % range_split)
    
    if not (len(range_split) in [1, 2]):
        pywikibot.output("Range parse fails: %s" % timestring)
        return create_time_spec("invalid")

    if len(range_split) == 1:
        at  = parseTimeValue(range_split[0])
        return {"at" : make_WbTime(at)}     
    else:
        _from = parseTimeValue(range_split[0])
        pywikibot.output("_from:%s" % list(_from))
        if range_split[1] == '':
            return {"from" :  make_WbTime(_from)}
        _to = parseTimeValue(range_split[1])
        pywikibot.output("_to:%s" % list(_to))
        if list(_to)[0] < 100: # abbreviated year
            Y, M, D, H, m, s, p = _to
            century = list(_from)[0] - (list(_from)[0] % 100)
            pywikibot.output("century:%s" % century)
            _to = (century + Y, M, D, H, m, s, p)
            pywikibot.output("new _to:%s" % list(_to))
        return {"from" : make_WbTime(_from),
                "to" :  make_WbTime(_to)}

def standard_time_handlers(pnum):
    """
    Returns (<interpret>, <check>) appropriate for <p number>
    Where
    <interpret> := fn(timestring) -> Instance of pywikibot.WbTime, whose
      year will be 0 if <timestring> could not be parsed.

    <check> := fn(wbTime) -> True iff <wbTime> is a valid time value
    """

    def corrected_times(parsed, next_time):
        print ("next time:%s" % next_time)
        # sometimes a two-character year needs to prepend the century
        # from the previous entry, presumed to be a year.
        m = re.match("^[0-9]{2}$", next_time)
        if m:
            if not re.match("^[0-9]{4}$", parsed[-1]):
                parsed[-1] = 'invalid'
                return parsed + ['invalid']
            next_time = parsed[-1][:2] + next_time
            print ("corrected time:%s" % next_time)
        return parsed + [next_time]
                   
        #parsedSpec = parseTimeValue(timestring)
    def get_WbTimes(value):
        value = re.sub("<ref>.*</ref>", "", value)
        value = value.replace(u'–', u'-') 
        value = value.replace(u'&ndash;', u'-') # stupid dashes
        pywikibot.output("starting time with value %s" 
                          % (value))
        # timestrings = re.split(br_delimiter, value)
        timestrings = parse_timestrings([], value)
        # pywikibot.output("timestrings in gwbtimes:%s" % timestrings)
        result = []
        for timestring in timestrings:
            if type(timestring) == type([]):
                result = result + [[create_time_spec(t)
                                    for t 
                                    in reduce(corrected_times,
                                               timestring,
                                               [])]]
            else:
                ## pywikibot.output("about to create time for %s" % timestring)
                result = result + [create_time_spec(timestring)]

        return result

    def check_WbTime(wbTime):
        # True iff wbTime is well-formed
        # TODO add more checks
        if wbTime.year == 0:
            return False
        # if wbTime.year < 100:
        #     return False
        return True

    # {"at"|"from"|"to" : wbTime}
    def check_WbTimes(wbTimes):
        # timespec or list of timespecs
        if type(wbTimes) == type([]):
            for w in wbTimes:
                if not check_WbTimes(w):
                    return False
            return True
        for key, wbTime in wbTimes.items():
            if not check_WbTime(wbTime):
                return False
        return True
            
        # put p-number specific stuff here
        # default:
    return (get_WbTimes, check_WbTimes)

# GLOBAL COORDINATES 
def standard_global_coordinate_handlers(pnum):
    """
    Returns (<interpret>, <check>) appropriate for <p number>
    Where
    <interpret> := fn(global_string) -> pywikibot.Coordinate
    <check> := fn(Coordinate) -> True iff the <coordinate> is valid 
      and suitable for <p number>
    """

    def polarityFor(direction):
        # return 1 or -1, for <direction>
        # where <direction> in {NEKD, SWGB}, matching English
        # and Turkish abbreviations
        # TODO: Move language-specific stuff to the supporting ontology
        if direction == "":
            return 1
        if direction.upper() in "NEKD":
            return 1
        if direction.upper() in "SWGB":
            return -1
        raise Exception("What polarity for %s" % direction)

    def dms2dd(degrees, minutes, seconds, direction):
        # translates <degrees>,<minutes>, <seconds>, <direction> to a
        # single decimal value
        degrees = float(degrees)
        minutes = float(minutes)
        seconds = float(seconds)
        polarity = polarityFor(direction)
        return polarity * (degrees + minutes/60 + seconds/(60*60))

    def latLongRe(latLongFormat, 
                  prefix = "[^0-9\-]*", 
                  inter="[^0-9\-]*"):
        # returns a regex that recognizes lat/long specification
        template = ur"{{Prefix}}{{LatLongFmt}}{{Inter}}{{LatLongFmt}}.*"
        regex = pystache.render(template,
                                {"Prefix" :prefix,
                                 "Inter" : inter,
                                 "LatLongFmt" : latLongFormat})
        pywikibot.output("latlong regex: %s" % regex)
        return re.compile(regex, re.IGNORECASE)

    def directionalLatLongRe(latLongFormat, NS, EW, 
                             prefix = "[^0-9\-]*", inter="[^0-9\-]*"):
        # returns a regex that recognizes lat/long combinded with NSEW 
        # specs. E.g. ???
        # todo: consider refactoring so that NS/EW stuff is informed by
        # supporting ontology or WD queries
        template = (
            ur"{{Prefix}}{{LatLongFmt}}.*{{NS}}{{Inter}}{{LatLongFmt}}.*{{EW}}.*")
        regex = pystache.render(template,
                                {"Prefix" : prefix,
                                 "Inter" :  inter,
                                 "LatLongFmt" : latLongFormat,
                                 "NS" : NS,
                                 "EW" : EW })
        # pywikibot.output("regex in dllr: %s" % regex)
        return re.compile(regex, re.IGNORECASE)

    def parseCoordinates(coordinateString):
        # returns (lat, long, precision)  from coordinateString
        # pywikibot.output("coords:%s" % (coordinateString))
        # in order of increasingly inclusive match...
        # Degree-minute-second...
        # D|M|S...
        #sometimes the seconds are decimals...
        degreeMinuteSecondDec = (
            "([0-9\-]+)\|([0-9\-]+)\|([0-9\-]+\.[0-9\-]+)")
        dmsdNERe =  directionalLatLongRe(degreeMinuteSecondDec, 
                                         "(N|S)", 
                                         "(E|W)")
        match = dmsdNERe.match(coordinateString)
        if match:
            pywikibot.output("matched dms decimal")
            (latD, latM, latS, latDir, 
             longD, longM, longS, longDir) = match.groups(0)
            latDecimal = dms2dd(latD, latM, latS, latDir)
            longDecimal = dms2dd(longD, longM, longS, longDir)
            return (latDecimal, longDecimal, 0.0001)   
        # else we keep checking other formats
        # sometimes the seconds are whole numbers...
        degreeMinuteSecond = "([0-9\-]+)\|([0-9\-]+)\|([0-9\-]+)"
        dmsNERe = directionalLatLongRe(degreeMinuteSecond, 
                                       "(N|S)", 
                                       "(E|W)")
        match = dmsNERe.match(coordinateString)
        if match:
            pywikibot.output("matched dms whole number & direction")
            (latD, latM, latS, latDir, 
             longD, longM, longS, longDir) = match.groups(0)
            latDecimal = dms2dd(latD, latM, latS, latDir)
            longDecimal = dms2dd(longD, longM, longS, longDir)
            return(latDecimal, longDecimal, 0.001)   
        # else we try other formats

        degreeCircleMinuteTickSecondTicks = (
            ur"(-?[0-9]+)°[^-0-9]*(-?[0-9]+)[′'][^-0-9]*(-?[0-9]+)[″\"]")

        dcmtsttDirRe = directionalLatLongRe(
            degreeCircleMinuteTickSecondTicks,
            "(N|S|K|G)",
            "(E|W|D|B)")
        match = dcmtsttDirRe.match(coordinateString)
        if match:
            pywikibot.output("matched dms symbols with direction")
            (latD, latM, latS, latDir, 
             longD, longM, longS, longDir) = match.groups(0)
            latDecimal = dms2dd(latD, latM, latS, latDir)
            longDecimal= dms2dd(longD, longM, latS, longDir)
            return (latDecimal, longDecimal, 0.0001)
        # else we try other formats
        # Degree-minute ...
        # sometimes its just lat | long...
        degreeCircleMinuteTick = ur"(-?[0-9]+)°.*(-?[0-9]+)[′']"
        dcmtDirRe = directionalLatLongRe(degreeCircleMinuteTick,
                                    "(N|S|K|G)",
                                    "(E|W|D|B)")
        match = dcmtDirRe.match(coordinateString)
        if match:
            pywikibot.output("matched dm symbols with direction")
            (latD, latM, latDir, longD, longM, longDir) = match.groups(0)
            latDecimal = dms2dd(latD, latM, 0, latDir)
            longDecimal= dms2dd(longD, longM, 0, longDir)
            return (latDecimal, longDecimal, 0.01)
        # else we try other formats

        dcmtRe = latLongRe(degreeCircleMinuteTick)
        match = dcmtRe.match(coordinateString)
        if match:
            pywikibot.output("matched dm symbols no direction")
            (latD, latM, longD, longM) = match.groups(0)
            latDecimal = dms2dd(latD, latM, 0, "")
            longDecimal= dms2dd(longD, longM, 0, "")
            return (latDecimal, longDecimal, 0.01)

        # else we try other formats
        decimal = "(-?[0-9]+\.[0-9]+)"
        decimalDirRe = directionalLatLongRe(decimal,
                                            "(N|S|K|G)",
                                            "(E|W|D|B)")
        match = decimalDirRe.match(coordinateString)
        if match:
            pywikibot.output("matched decimal & dir")
            (latitude, latDir, longitude, longDir) = match.groups(0)
            latDecimal = polarityFor(latDir) * float(latitude)
            longDecimal= polarityFor(longDir) * float(longitude)
            return (latDecimal, 
                    longDecimal, 
                    0.0001)

        # else we try other formats
        decimalRe = latLongRe(decimal)
        match = decimalRe.match(coordinateString)
        if match:
            pywikibot.output("matched two decimals")
            (latitude, longitude) = match.groups(0)
            latDecimal = float(latitude)
            longDecimal= float(longitude)
            return (latDecimal, 
                    longDecimal, 
                    0.001)

        # else we try other formats
        degreeMinute = "([0-9\-]+)\|([0-9\-]+)"
        dmDirRe = directionalLatLongRe(degreeMinute,
                                       "(N|S|K|G)",
                                       "(E|W|D|B)")
        match = dmDirRe.match(coordinateString)
        if match:
            pywikibot.output("matched degree/minute and direction")
            (latD, latM, latDir, longD, longM, longDir) = match.groups(0)
            latDecimal = dms2dd(latD, latM, 0, latDir)
            longDecimal= dms2dd(longD, longM, 0, longDir)
            return (latDecimal, longDecimal, 0.01)

        # else we try one more format...
        dmRe = latLongRe(degreeMinute)
        match = dmRe.match(coordinateString)
        if match:
            pywikibot.output("matched degree and minute")
            (latitude, longitude) = match.groups()
            latDecimal = float(latitude)
            longDecimal= float(longitude)
            return (latDecimal, 
                    longDecimal, 
                    0.1)
        pywikibot.output("'%s' could not be parsed for coordinates" 
                         % coordinateString)
        return (None, None, None)
        # end of parseCoordinates

    def get_coordinates(value):
        # returns an instance of pywikibot.Coordinates for <value>
        # or None if the parse failed
        value = value.strip()
        (latitude, longitude, precision) = parseCoordinates(value)
        pywikibot.output("coordinate args: %s %s %s" 
                         % (latitude, longitude, precision))
        if not (latitude and longitude and precision):
            return None
        return [pywikibot.Coordinate(latitude, 
                                     longitude, 
                                     precision = precision)]

    def non_null_coordinates(coordinates):
        # fail if <coordinates> is null
        if not coordinates:
            return False
        return True

    # put pnum-specific handling here
    # default...
    return (get_coordinates, non_null_coordinates)

# COMMONS MEDIA (incomplete)

def standard_commons_media_handlers(pSpec):
    def get_image(value):
        commonssite = pywikibot.Site("commons", "commons")
        imagelink = pywikibot.Link(value, source=commonssite,
                                   defaultNamespace=6)
        image = pywikibot.FilePage(imagelink)
        if image.isRedirectPage():
            image = pywikibot.FilePage(image.getRedirectTarget())
        return image
    image_exists = lambda image: image.exists()
    return (get_image, image_exists)



##############################
# CLAIM CONSTRAINT TESTS
# 
# boolean tests which may be invoked to decide whether to include a claim 
# parsed from a template
##############################

def relationExists(parse_state):
    """
    Returns True iff there is already a claim 
    <item>, <claim>, <linked_item> in WD
    Where:
    <parse_state> := {?item ?claim ?target ...}
    <item> is a page assocated with some q-number
    <claim> is a claim associated with type wikibase_item
    <target> == <linked_item>
    <linked_item> is a page associated with a q-number
    """
    item, claim, linked_item = (parse_state[k]
                                for k in
                                ['item', 'claim', 'target'])
    template = """
    PREFIX wd: <http://www.wikidata.org/entity/>
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    Ask Where
    {
      {{S}} {{P}} {{O}}.
    }
    """
    query = pystache.render(template,
                            {"S" : "wd:" + item.getID(),
                             "P" : "wdt:" + claim.getID(),
                             "O" : "wd:" + linked_item.getID()})
    # pywikibot.output("pre-duplicate query:%s" % query)
    return askQueryWithRetries(query)

def checkForCycles(parse_state):
    """
    Returns True iff no cycle exists via <claim> from <linked item> 
      to <item>
    <parse_state> := {?item ?claim ?target ...}
    <item> is a page assocated with some q-number
    <claim> is a claim associated with type wikibase_item
    <target> == <linked_item>
    <linked_item> is a page associated with a q-number
    """
    item, claim, linked_item = (parse_state[k]
                                for k in
                                ['item', 'claim', 'target'])

    template = """
    PREFIX wd: <http://www.wikidata.org/entity/>
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    Ask Where
    {
      {{O}} {{P}}+ {{S}}.
    }
    """
    query = pystache.render(template,
                            {"S" : "wd:" + item.getID(),
                             "P" : "wdt:" + claim.getID(),
                             "O" : "wd:" + linked_item.getID()})
    pywikibot.output("cycles query:%s" % query)
    return not askQueryWithRetries(query)

def checkForCyclesAndOtherSubsumption(parse_state):
    """
    Returns True iff no cycle exists via <claim> from <linked item> to
      <item> and there is no assertion from another subsumption link.
    Only called to constrain subsumption(P31 and P279) assertions. This
      covers cases like  P31/P279/P31/...
    """
    item, claim, linked_item = (parse_state[k]
                                for k in
                                ['item', 'claim', 'target'])

    assert claim.getID() in ('P31', 'P279')

    template = """
    PREFIX wd: <http://www.wikidata.org/entity/>
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    Ask Where
    {
      { {{O}} {{P}}+ {{S}}. }
      Union
      { {{S}} (wdt:P31|wdt:P279)+ {{O}}.}
    }
    """
    query = pystache.render(template,
                            {"S" : "wd:" + item.getID(),
                             "P" : "wdt:" + claim.getID(),
                             "O" : "wd:" + linked_item.getID()})
    # pywikibot.output("cycles query:%s" % query)
    return not askQueryWithRetries(query)

def custom_constraint_fn(template):
    """
    Returns fn(parse_state) -> true iff <ask_query> for <template> is true
    Where
    <template> is a pystache template for <ask_query>, which may have 
      parameters for 'Prefixes" 'Subject" and/or 'Object'.
    <ask_query> must be a well-formed SPARQL ASK query
    NOTE: this is typically the value of a harvest:askQueryTemplate property
      in a harvest:CustomConstraint for some property specified in the 
      supporting ontology files.
    """
    def constraint_fn (pasrse_state):
        item, claim, linked_item = (parse_state[k]
                                    for k in
                                    ['item', 'claim', 'target'])

        query = pystache.render(template,
                                {"Prefixes" : CONFIG_PREFIXES,
                                 "Subject" : item.getId(),
                                 "Object" : lined_item.getID()
                                 })
        return askQueryWithRetries(query)
    return constraint_fn


def checkSubsumption (subject, parent):
    """
    Returns True iff <subject> is subsumed by <parent>
    Where
    <subject> := 'wd:Q...' is the URI for some Q-number
    <parent> := 'wd:Q...' is the URI for the Q-number of some class
    """
    # USING A UNION HERE BECAUSE BLAZEGRAPH IS SOMETIMES FLAKEY
    # ABOUT ITS HANDLING OF + IN PROPERTY PATHS
    template = """
        PREFIX wd: <http://www.wikidata.org/entity/>
        PREFIX wdt: <http://www.wikidata.org/prop/direct/>
        Ask Where
        {
          { {{S}} wdt:P31/wdt:P279* {{Class}}.}
          Union
          { {{S}} wdt:P279* {{Class}}.}
        }
        """
        # ... P31?/P279* was strangely dysfunctional. taking the union
        # to compensate
    query = pystache.render(template,
                            {"S" : subject,
                             "Class" : parent})
    # pywikibot.output("subsumption query:%s" % query)
    return askQueryWithRetries(query)


def time_range_constraint_fn ():
    """
    Return fn(parse_state) -> true iff linked item  of parse state is a
      time representation
    """
    def check_for_time (parse_state):
        (item, linked_item) = (parse_state[k]
                               for k in ["item", "target"])
        return isinstance(linked_item, pywikibot.WbTime)

    return check_for_time

def objectRangeConstraintFn(classUri):
    """
    Returns function fn(item, claim, linked_item) -> True iff 
      <linked item> is a member of <classUri>.
    """
    def rangeConstraint (parse_state): #(item, claim, linked_item):
        pywikibot.output("classUri:%s" % classUri)

        (item, linked_item) = (parse_state[k]
                               for k in ["item", "target"])
        pywikibot.output("linked_item:%s" % linked_item)
        def objectUri(o):
            # o :~ '[[wikidata:Q...]]'
            _o = str(o).replace("[[wikidata:", "wd:")
            return _o.replace("]]", "")
        # USING A UNION HERE BECAUSE BLAZEGRAPH IS SOMETIMES FLAKEY
        # ABOUT ITS HANDLING OF + IN PROPERTY PATHS
        template = """
        PREFIX wd: <http://www.wikidata.org/entity/>
        PREFIX wdt: <http://www.wikidata.org/prop/direct/>
        Ask Where
        {
              { {{O}} wdt:P31/wdt:P279* {{Class}}.}
              Union
              { {{O}} wdt:P279* {{Class}}.}
        }
        """
        query = pystache.render(template,
                                {"O" : objectUri(linked_item),
                                 "Class" : classUri} )
        pywikibot.output("rangeConstraint query:%s" % query)
        return askQueryWithRetries(query)
    return rangeConstraint


def objectIsGeoLocation(parse_state):
    """
    Returns True iff no cycle exists via <claim> from <linked item> to
      <item>
    """
    geographicLocationUri = "wd:Q2221906"
    rangeConstraint = objectRangeConstraintFn (geographicLocationUri)
    return rangeConstraint(parse_state)
    
def nonCyclingGeoLocation (parse_state):
    """
    Returns True iff <linked item> is a geo-location, and
      there is no located-in cycle back to <item>
    """
    # USING A UNION HERE BECAUSE BLAZEGRAPH IS SOMETIMES FLAKEY
    # ABOUT ITS HANDLING OF PROPERTY PATHS
    (item, linked_item) = (parse_state[k]
                           for k
                           in ["item", "target"])
    template = """
    PREFIX wd: <http://www.wikidata.org/entity/>
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    Ask Where
    {
      {
         { {{O}} wdt:P31/wdt:P279* wd:Q2221906.}
           Union
          { {{O}} wdt:P279* wd:Q2221906.}
      }
      Filter Not Exists { {{O}} wdt:P131/wdt:P131* {{S}} }
    }
    """
    query = pystache.render(template,
                            {"S" : "wd:" + item.getID(),
                             "O" : "wd:" + linked_item.getID()})
    # pywikibot.output("nonCyclingGeoLocation query:%s" % query)
    return askQueryWithRetries(query)

def nonCyclingAdminRegion (parse_state):
    """
    Returns True iff <linked item> is an admin region, and
      there is no located-in cycle back to <item>
    """
    (item, linked_item) = (parse_state[k]
                           for k in ["item", "linked_item"])
    # USING A UNION HERE BECAUSE BLAZEGRAPH IS SOMETIMES FLAKEY
    # ABOUT ITS HANDLING OF + IN PROPERTY PATHS
    template = """
    PREFIX wd: <http://www.wikidata.org/entity/>
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    Ask Where
    {
        {
           { {{O}} wdt:P31/wdt:P279* wd:Q56061.}
           Union
           { {{O}} wdt:P279* wd:Q56061.}
        } 
        Filter Not Exists { {{O}} wdt:P131/wdt:P131* {{S}} }
    }
    """
    query = pystache.render(template,
                            {"S" : "wd:" + item.getID(),
                             "O" : "wd:" + linked_item.getID()})
    pywikibot.output("nonCyclingAdminRegion query:%s" % query)
    return askQueryWithRetries(query)



        
def claimForPropertyExists(context, pnum):
    """
    Returns True iff a claim for <pnum> exists in <context>
    Where
    <context> := {?claims, ?itemContents, ...} as retrieved for some item,
      and/or parsed from a template
    <claims> := [<claimSpec>, ...]
    <pnum> "P...", names a WD property.
    <claimSpec> := (<action>, <page>, <item>, <claim>)
    """

    if ('itemContents' not in context 
        or 'claims' not in context['itemContents']):
        return False
    if pnum in context['itemContents']['claims']:
        return True
    return ('claims' in context and pnum in context['claims'])


def checkNativeConstraints (p_number, obj):
    """
    Returns True iff <obj> complies with native range constraints for 
    <p number> False if there are no native range constraints.
    Where
    A native range constraint is one defined in WD itself.
    <p number> is a WD predicate ID number
    <obj> is the Q-number of some entity in wikibase, typically parsed from a
      template.
    """
    print ("p_number in cnc:%s" % p_number)
    print ("Obj type in cnc:%s" % type(obj))
    print ("Obj in cnc:%s" % obj)
    def wd_uri(id):
        return "wd:" + id

    template = """
    {{{Prefixes}}}
    Ask Where
    { 
      {
        # query for property constraints declared in WD
        Select ?class 
        { 
          {{WDProperty}} p:P2302 ?propertyConstraint.
          ?propertyConstraint ps:P2302 wd:Q21510865; #value Type Constraint
            pq:P2308 ?class; 
            pq:P2309 wd:Q21503252. # specifies must be instance of ?class
        }
      }
      { {{O}} wdt:P31/wdt:P279* ?class.}
      Union
      { {{O}} wdt:P279* ?class.}
    }
    """
    # ... P31?/P279* was strangely dysfunctional. taking the union to 
    # compensate
    constraint = pystache.render(template,
                                 {"Prefixes" : CONFIG_PREFIXES,
                                  "O" : wd_uri(obj),
                                  "WDProperty" : wd_uri(p_number)
                                  })
    pywikibot.output("range constraint query:%s" % constraint)
    return askQueryWithRetries(constraint)


#########################################################################
# AGGREGATORS 
# 
# Functions that return a modified API spec based on new information parsed 
# from some template
# These functions should support a function call with the following 
#  arguments:
# (page_parse, field_parse)
# Where
# <page_parse> := {?itemContents ?claims, ...}, plus any other annotation 
#  that pertains to the currently parsed template that may need to be
#  referenced in order to properly interpret the specific template 
#  field currently being parsed.
# <claims> := [<action spec>, ...]
# <action spec> := <field_parse> << {?action, ...}
# <field_parse> := {?page ?item ?claim ?target ...} plus any other annotation
#   that pertains to the specific template parameter being parsed.
# <page> is the WP page containing some template
# <item> is the WD Q-number associated with <page>
# <claim> is a fresh claim associated with some p-number
# <target> is a candiate target for <claim>

#########################################################################

def resolve_qualifier_conflict(page_parse, field_parse, qualified, conflicting_qualifiers):
    """
    Returns (<page_parse>, <qualified>) modified per <field_parse> and
      <conficting_qualifiers>
    Where
    <page_parse> is the current state of the page parse, modified s.t.
      it is appropriate to the return value of <qualified>
    <qualified> as input is an action spec for a top-level claim, whose
      qualifiers contain <conflicting_qualifiers>. A return value of None
      indicates that <claim> should not be asserted as an additional qualifier.
      If returned in non-null, it must quarantee that <page_parse> no longer
      harbors a set of conflicting_qualifiers.
    <field_parse> is the parse of the current template field, associated with
      a qualifier
    <conflicting_qualifiers> := [<conflicting_qualifier>, ...]
    <conflicting_qualifier> := {action : "qualify", 'qualifier_pnum' : <p> ...}
    <p> is the same property id as <field_parse> ['qualifier_pnum'], hence the
      conflict.
    
    """

def defer_to_existing_qualifiers (page_parse, field_parse, qualified, conflicting_qualifiers):
    """
    The default value of the resolve_qualifier_conflict argument to the
    install_qualifiers_function.
    Returns (<page_parse>, None), indicating that <field_parse> should
      not be installed as a qualifier, defering the conflicting qualifier(s)
      already installed.
    """
    print ("qualifier_pnum:%s" % field_parse['qualifier_pnum'])
    print ("value:%s" % field_parse['value'])
    print ("conflicting_qualifiers:%s" % conflicting_qualifiers)
    print ("letting the existing state stand")
    return (page_parse, None)
    
def install_qualifiers(page_parse, field_parse):

    """
    Returns <page_parse> << {"claims" : {<qualified pnum> [<action_spec>, ...],
                                         ...}
                              ...}
    Such that <action_spec> << {"qualifiers" : {<qp> : <qualifier>, ...}, ...}
    WHERE
    <page_parse> is the ongoing parse of <page>
    <field_parse> := {?qualified_field ?ith ?out_of ?qualified_pnum
                      ?cloneClaimFn ?page ?item ?claim ?target ?checker
                      ?group ?choose_qualified_claim
                      ?resolve_qualifier_conflict
                      ...
                     }
    <page> is the page being parsed
    <item> is the WD Q-entity being annotated
    <target> is the claim being parsed from the template, which may be
      a qualifier on the claim associated with <qualified_pnum>
    <qualified_pnum> names the pnum associated with the top-level claim
      which <target> may be qualifying
    <action_spec> is a <field_parse> instance inferred earlier from some
      other field, with an "action" field = "add", annotations on a
      top-level claim which may be qualified
    <qualifiers> := {<qp> : <qualifier>, ...}
    <qp> a p-number for a qualifier, such as the one associated with
      'start time'
    <qualifier> := a <field_parse> instance s.t. "action" == "qualify"
    <checker> := fn(claim) -> true if constraints are met
    <choose_qualified_claim> and
    <resolve_qualifier_conflict> are discussed in the CONFLICT_RESOLUTION
      section below.

    CONFLICT RESOLUTION
    The two functions described below are invoked in the relatively
      rare cases where there are amgiguities or conflicts in play
      when parsing a template.

    When more than one 'add' action spec may be a candidate for qualification:
    <choose_qualified_claim> := fn(page_parse, qualified_claims)
       -> (page_parse, _qualified) s.t. the ambiguity expressed by the
       plurality of <qualified_claims> has been resolved. See CONFLICT
       RESOLUTION section below.

    When for the targeted 'add' action spec there is already a qualifier
      installed which conflicts with the qualifier specified by <field_parse>:
    
    <resolve_qualifier_conflict> := fn (
            page_parse,
            field_parse,
            qualified,
            conflicting_qualifiers)
            ->
            (page_parse, qualified), s.t:
            case 1: qualified == None -- let the current status stand and do
              not install the qualifier under consideration
            Case 2: qualified is Non-null -- <page_parse> and <qualified>
              have been updated so as not to give rise to <conflicting_qualifiers>
    <qualified> is the action spec matching the qualifier at hand.
    <conficting_qualifiers> := [<conflictin_qualifier>, ...]
    <conflicting_qualifier> is an qualifier action spec already installed for
      <qualified> which conflicts with <field_parse>

    """
    page, item, claim, target, checker = (
        field_parse[k] for k in ["page", "item", "claim", "target", "checker"])

    qualified_pnum, ith, out_of= (field_parse[k] 
                                  for k in ["qualified_pnum", "ith", "out_of"])
                                            
    qualified_field = field_parse.get('qualified_field', None)
    choose_qualified_claim = field_parse.get('choose_qualified_claim', None)
    resolve_qualifier_conflict = field_parse.get('resolve_qualifier_conflict',
                                                 defer_to_existing_qualifiers)
    
    existing_edit_specs = page_parse.get('claims', {})
    # {<p> : [<action_spec>, ...], ...}
    
    qualified_claims = existing_edit_specs.get(qualified_pnum, [])

    def qualifiers_of(qualified):
        return qualified.get("qualifiers", [])

    def get_conflicting_qualifiers(qualifed):
        return [q for q in qualifiers_of(qualified)
                if q['claim'].getID()
                == claim.getID()]
    
    if len(qualified_claims) == 0:
        pywikibot.output ("No qualified claims. Qualification fails.")
        return page_parse


    if not checker(field_parse):
        pywikibot.output("checker failed in install_qualifiers. Skipping")
        return existing_edit_specs

    qualified_claim = None

    if len(qualified_claims) == 1:
        qualified = qualified_claims[0]
    else:
        page_parse, qualified = choose_qualified_claim(page_parse,
                                                       qualified_claims)

    print ("qualifiers:%s" % qualifiers_of(qualified))
    conflicting_qualifiers = get_conflicting_qualifiers(qualified)

    if len(conflicting_qualifiers) > 0:
        page_parse, qualified = resolve_qualifier_conflict(
            page_parse,
            field_parse,
            qualified,
            conflicting_qualifiers)
        if qualified:
            assert (len(get_conflicting_qualifiers(qualified)) == 0)
    
    pywikibot.output("qualified:%s" % qualified)

    if not qualified:
        return page_parse
    # else there is exactly one qualified, an 'add' action
    claim.setTarget(target)
    pywikibot.output("qualified has target:%s" % qualified['target'])

    entry = qualifiers_of(qualified)
    pywikibot.output("qualified has qualifiers:%s" % 
                     [[q['claim'].getID(),
                       q['claim'].getTarget()]
                      for q in entry])
    print("adding qualifier for value :%s" % field_parse['value'])

    qualified['qualifiers'] = entry + [
        merge(
            field_parse,
            {"action" : "qualify"})]
    assert qualified in page_parse['claims'][qualified['claim'].getID()] 
    assert len(qualified['qualifiers']) == len(entry) + 1

    # pywikibot.output("existing actions at end of iq:%s" % existing_edit_specs)
    return page_parse
    

def addIfItemHasCorroboratingClaim (page_parse, field_parse):
    """
    Returns <page_parse> << {?claims + [...<action>], ...} 
      only if <item> <corroboratingP> <corroboratingO> can be found
      in WD or in <newClaims>, e.g. If we're going to assert that 
      <item> has-profession <politician> we should confirm that
      <item> holds-office <political office> before we add the claim
    Where
    <page_parse> := {?itemContents ?claims, ...}
    <field_parse> := {?claim ?item ?target ?corroboratingP ?corroboratingO, ...}
    <item> is a WD item
    <claim> is claim about <item> being constraint-tested
    <target> is the object of the constraint being tested
    <corroboratingP> is a P-number for a property 
    <corroboratingO> is a Q-number for a class that subsumes a correct
      object for <corroboratingP>
    <claims> := {<pnum> : [<claimSpec>, ...], ...}
    <claimSpec> := (<action>, <page>, <item>, <claim>)
      is a specification for a claim parsed from the template.
    """
    raise Exception ("This probably needs to be refactored. Looks like you found a test case.")
    
    newClaims = (page_parse['claims'] 
                 if 'claims' in page_parse 
                 else [])
    pywikibot.output("newClaims:%s" % newClaims)

    def claimPConfirms(claim):
        return (field_parse['claim'].getID() 
                == field_parse['corroboratingP'])

    def claimSubsumptionConfirms (claim):
        return checkSubsumption(
            "wd:%s" % claim.getTarget().getID(), 
            "wd:%s" % corroboratingO)

    corroboratingP, corroboratingO, item = (field_parse[k] 
                                            for k in ['corroboratingP', 
                                                      'corroboratingO',
                                                      'item'])

    if ((corroboratingP in newClaims
         and any([new_claim 
                  for new_claim  
                  in (n['claim']
                      for n 
                      in newClaims[corroboratingP])
                  if claimSubsumptionConfirms(new_claim)])

        or 
        (corroboratingP in item.get('claims')
         and any ([existing_claim
                   for existing_claim 
                   in page_parse['itemContents'][corroboratingP]
                   if claimSubsumptionConfirms(existing_claim)])))):

        
        return addClaimSpec(page_parse, 
                            merge(field_parse,
                                  {"action" : "add"}))

    # else no change...
    return page_parse

# Typical default function in tournament-style transductions
default_to_defender=lambda defender, challenger, check: defender


def preferMoreSpecificNewClaimForTransitiveProperty (defender_parse, 
                                                     challenger_parse):

    """
    Returns <defender_parse> or <chalenger_parse>, depending on which is more 
      specific following transitive links of <pnum>
    Where:
    <pnum> refers to a transitive relations like P31 or P131.
    <defender_parse> := {?claim ...} which MAY
      be a member of <existingActions>
    <challenger_parse> := {?claim ?target, ...}
    NOTE: this is typically called in an aggregator function as a
      'chooseNewClaim' parameter, called when more than one claim parsed
      from the template is mapped to the same P-number. 
    """

    def objectUri(o):
        # o :~ '[[wikidata:Q...]]'
        _o = str(o).replace("[[wikidata:", "wd:")
        return _o.replace("]]", "")

    pnum = challenger_parse['claim'].getID()

    template = """
    Ask Where
    {
      {{ChallengerQ}}} wdt:{{P}}+ {{Defender_ParseQ}}.
    }
    """
    query = pystache.render(template,
                            {"ChallengerQ" : objectUri(
                                challenger_parse['target']),
                             "P" : pnum,
                             "Defender_ParseQ" : objectUri(
                                 defender_parse['claim'].getTarget())})
    # pywikibot.output("query in pmsncftp:%s" % query)
    if askQueryWithRetries(query):
        return challenger_parse
    return defender_parse

def preferExistingClaim(page_parse, field_parse, 
                        chooseNewClaim=default_to_defender):

    """
    The default aggregator.
    Returns <page_parse> << {claims: {<pnum> : [<claim>], ...},...}, 
      adding only a single  claim for P-number if does not already 
      exist in <itemContents>
    <page_parse> := {?itemContents, ?claims, ...}
    <itemContents> := {<p-number> : [<claimSpec>, ...], ...}, already existing
      claims
    <field_parse> := {?page, ?item, ?claim, ?target ?checker, ...}
    <claimSpec> := {?item ?claim ...}
    <checker> := fn(item, claim, linked_item) -> true iff the assertion
      would be valid and meet constraints
    <chooseNewClaim> := fn(defender, challenger, check) -> <winner>
      in cases where there is no existing claim and more than
      one contender for the P-number was parsed from the template
    <winner> may add <newClaim> to <claims> if appropriate
    """
    # pywikibot.output("starting spec for %s" % field_parse)
    # pywikibot.output("claim keys:%s" % page_parse['itemContents']['claims'].keys())
    
    [pnum, value] = [field_parse[k] for k in ['prop', 'value']]
    # pywikibot.output("pnum in pec:%s" % pnum)
    # pywikibot.output("value in pec:%s" % value)
    if ('itemContents' in page_parse 
        and pnum in page_parse['itemContents']['claims']):
        pywikibot.output("claim for %s already exists. Skipping." 
                         % pnum)
        return page_parse

    if 'checker' in field_parse and field_parse['checker'](field_parse):
        if 'claims' in page_parse and pnum in page_parse['claims']:
            winner = chooseNewClaim(page_parse['claims'][pnum], field_parse)
            if winner == field_parse:
                page_parse['claims'][pnum] = []
                return addClaimSpec (page_parse, 
                                     merge(field_parse,
                                           {"action" : "add"}))
            pywikibot.output("There's already a suitable new claim.")
            return page_parse
        else: # we passed and there's no other claim
            return addClaimSpec (page_parse, 
                                 merge(field_parse,
                                       {"action" : "add"}))
            
    #...else no existing, but constraint checker fails...
    pywikibot.output("value %s fails constraint %s for %s. Skipping." 
                     % (field_parse['target'],
                        field_parse.get("checker", None),
                        pnum))
    if not'checker' in field_parse:
        pywikibot.output("WARNING: NO CHECK FOR %s in preferExistingClaim"
                         % pnum)
    return page_parse

def preferExistingAndMoreSpecificNewbies(page_parse, field_parse):
    """
    Returns <page_parse> with <field_parse> added as a new claim spec if
    there is not already a claime for field_parse's p-number in <itemContents>
    and there is not already a claim with <= specificity.
    """

    return preferExistingClaim(
        page_parse, 
        field_parse,
        chooseNewClaim = preferMoreSpecificNewClaimForTransitiveProperty)

def addIfNotRedundant(page_parse, field_parse):
    """
    Returns <page_parse> << {'claims' : {<p> : [<newAction>]}}
      if there is not already a claim with same property and target in 
      claims already associated with the page.
    """

    pnum, check = (field_parse[k]
                   for k in ['prop', 'checker'])
    actions = page_parse.get('claims', None)
    existing_claims = page_parse['itemContents']['claims']

    def is_redundant():
        def is_matching_claim(claim):
            return (claim.getTarget().getID() 
                    == field_parse['target'].getID())

        if actions:
            matching_claims = [n 
                               for n in actions.get(pnum, [])
                               if is_matching_claim(n.get('claim'))]
        
            if len(matching_claims) > 0:
                return True

        matching_claims = [n 
                           for n
                           in existing_claims.get(pnum, [])
                           if is_matching_claim(n)]
        
        return len(matching_claims) > 0
    if is_redundant():
        pywikibot.output("redundant. not adding claim")
        return page_parse
    pywikibot.output("not redundant. checking claim")
    if not check(field_parse):
        pywikibot.output("Failed check. not adding claim")
        return page_parse
    pywikibot.output("constraint test passed. Adding")
    return addClaimSpec(page_parse, 
                        merge(field_parse,
                              {"action" : "add"}))

def implicit_field(prop):
    """
    Returns a string naming a pseudo-field for an implicit claim
    """
    return "implicit_%s" % prop

def is_implicit_field(field):
    """
    Returns true iff <field> is an implicit pseudo-field
    """
    return re.match("^implicit.*", field)

def get_aggregation_fns (supporting_ontology, run_name):
    """
    Returns {?fields ?properties}  drawn from <supporting_ontology>
    Where
    <fields> := {<field> <aggregator>...}
    <properties> := { <p> : <aggregator> ...}
    <p> is a p-number for some property
    <aggregator> := fn(<page-parse> <field_parse>) -> <page_parse>
      s.t. <page_parse> may have added claims specified in <field_parse>
      appropriately.
    <supporting_ontology> is an RDF graph informed by command-line arguments.
    """

    q = """
    {{{Prefixes}}}
    Select Distinct ?aggregated ?specType ?specKey ?aggregator ?chooseNew
    Where
    {
        {
          # implicit
          ?run harvest:implicitSpec ?aggregated.
          Filter Regex(Str(?run), "{{run_name}}", "i")
          ?aggregated harvest:aggregation ?aggregator;
            harvest:property ?property.
          Bind ("implicit" as ?specType)
          Bind (Replace(Str(?property), "http://www.wikidata.org/.*/P", "P")
                as ?specKey)
        }
        Union
        {
          # field 
          ?run harvest:fieldSpec ?aggregated.
          Filter Regex(Str(?run), "{{run_name}}", "i")
          ?aggregated harvest:field ?field;
            harvest:aggregation ?aggregator.
          Bind ("field" as ?specType)
          Bind (Replace(Str(?field), Str(harvest:), "") as ?specKey)
        }
        Union
        {
           # property specs
           ?aggregated harvest:aggregation ?aggregator.
            Filter Regex(Str(?aggregated), "http://www.wikidata.org/.*/P")
           Bind("property" as ?specType)
           Bind (replace(Str(?aggregated), "http://www.wikidata.org/.*/P", "P")
                 as ?specKey)
        }
        Optional
        {
          ?aggregated harvest:chooseNew ?chooseNew.
        }
    }
    """
    q = pystache.render(q,
                        {"Prefixes" : CONFIG_PREFIXES,
                         "run_name" : run_name
                        })
    print ("q:%s" % q)
    def choose_new_fn (chooseNew):
        # returns fn(this, that) -> either <this> or <that>
        # where <this> and <that> are competing values parsed
        # from the current template.
        if (chooseNew == "PreferMoreSpecific"):
            return preferMoreSpecificNewClaimForTransitiveProperty
        elif (chooseNew == None or chooseNew == "ChooseArbitrarily"):
            return default_to_defender
        else:
            raise Exception ("Fell through with chooseNew %s" % chooseNew)
        
    def aggregator_fn (aggregator, chooseNew):
        # returns fn(page_parse, field_parse) -> page_parse
        if (aggregator == "PreferExistingClaim"):
            def _preferExistingClaim (page_parse, field_parse):
                preferExistingClaim(page_parse, field_parse,
                                    chooseNewClaim=choose_new_fn(chooseNew))
            return _preferExistingClaim
        elif (aggregator == "AddIfNotRedundant"):
            return addIfNotRedundant
        else:
            raise Exception ("Fell through with aggregator spec %"
                             % aggregator)
        
    def update (acc, p_f, aggregated, aggregator):
        _p_f = acc.get(p_f, {})
        _p_f[aggregated] = aggregator
        acc[p_f] = _p_f
        return acc
    
    wd_re = re.compile("http://www.wikidata.org/.*/")
    harvest_re = re.compile ("http://naturallexicon.org/harvest/#")
    def collect_aggregation_policy (acc, next_binding):
        # returns acc := {?fields ?propertiess}
        [aggregated,
         specType,
         specKey,
         aggregator,
         chooseNew] = [str(x) for x in next_binding]
        
        aggregated = wd_re.sub("", aggregated)
        aggregator = harvest_re.sub("", aggregator)
        chooseNew = (harvest_re.sub("", chooseNew)
                     if chooseNew else None)

        if (specType=="property"):
            return update(acc,
                          "properties",
                          specKey,
                          aggregator_fn(aggregator, chooseNew))
        elif (specType=="implicit"):
            return update(acc,
                          "fields",
                          implicit_field (specKey),
                          aggregator_fn(aggregator, chooseNew))
            
        elif (specType=="fields"):
            return update(acc,
                          "fields",
                          specKey,
                          aggregator_fn(aggregator, chooseNew))
                
        else:
            raise Exception("Fell through on specType %s" % specType)

        return acc
    
    policies = {}
    for r in supporting_ontology.query(q):
        policies = collect_aggregation_policy (policies, r)
    return policies


##################################################
# API SPECIFICATIONS 
# Specifies changes to make through the WB API
##################################################


# Labels and aliases...
def collectLabelAndAliasEdits (itemContents_changedFields, label):
    """
    Returns (<itemContents>, <changedFields>), appropriate to <label>
    Where
    <itemContents> := {?labels ?aliases ...}, per the output of a call to 
      item.get() which may have <label> added to <labels> or <aliases> as 
      appropriate
    <changedFields> := set([<'labels' if changed and/or 'aliases' if changed>])
    <label> is a string extracted from a template which was inferred to 
      be a member of  <labels> or <aliases>
    <labels> := {<lang> : <label>, ...}
    <aliases> := {<lang> : [<label>,...], ...}
    <lang> is the language associated with the source wikipedia.
    """
    # pywikibot.output("label in collectLabelAndAliasEdits:%s" % label)
    itemContents, changedFields = itemContents_changedFields
    lang = pywikibot.config.mylang
    invalidNameRe = re.compile(".*[\[\]\"<>(){}].*")
    def prefer(defender, challenger):
        # returns [(<value>, <field>), ...], or [] if no changes
        # where 
        # <value> is in {<defender>, <challenger>} and should be added to 
        #     <field>
        # <field> is in {"labels", "aliases"}
        # <defender> is existing label, possibly None
        # <challenger> is a label parsed from the template
        # NOTE: will prefer defender for <labels>, unless it contains a ','
        #    or '(' or something
        # pywikibot.output("defender:%s challenger:%s" % (defender,challenger))
        # pywikibot.output("choosing between %s and %s" 
        #                    % (defender,challenger))
        challenger = challenger.strip("'''")
        def preCommaMatchesChallenger():
            # true if challenger matches defender up to a comma in defender
            return (defender.split(',')[0].strip().lower() 
                    == challenger.lower())
        def preParenMatchesChallenger():
            # true if challenger matches defender up to a '(' in defender
            return (defender.split('(')[0].strip().lower() 
                    == challenger.lower())

        # pywikibot.output("defender:%s. challenger:%s" % (defender, challenger))
        if not defender:
            return [(challenger, "labels")]
        if invalidNameRe.match(challenger):
            return [] # no changes
        if defender.lower() == challenger.lower():
            return [] # no changes
        if (',' in defender 
            and ',' not in challenger 
            and preCommaMatchesChallenger):
            return [(challenger, "labels"), (defender, 'aliases')]
        if ('(' in defender 
            and '(' not in challenger 
            and preParenMatchesChallenger):
            return [(challenger, "labels"), (defender, 'aliases')]
        return [(challenger, "aliases")]

    def aliasLength(_itemContents):
        # used to detect a change
        if lang not in _itemContents['aliases']:
            return 0
        return len(_itemContents['aliases'][lang])

    def updateLabels(_itemContents, value):
        # returns <_itemContents> << {'labels' : {<lang> : <value}}
        # Where
        # <_itemContents> starts as {}
        _itemContents['labels'] = {lang : value}
        return _itemContents

    def updateAliases(_itemContents, value):
        # pywikibot.output("label in update aliases:%s" % value)
        # Returns (<itemContents>+, <isNewAlias>)
        # Where 
        # <itemContents> may have <value> added to aliases, 
        # <isNewAlias> is True iff the alias wasn't already there
        # beginningAliasLength = aliasLength(_itemContents)

        def appendNewAlias(existingAliases):
            to_lower = lambda x : x.lower()
            if value.lower() in [to_lower(a) for a in existingAliases]:
                pywikibot.output("%s is already in aliases" % value)
                return existingAliases
            pywikibot.output("adding %s to aliases" % value)
            return existingAliases + [value]
        aliasesDict = _itemContents.get('aliases', {})
        existingAliases = aliasesDict.get(lang, [])
        priorAliasCount = len(existingAliases)
        existingAliases = appendNewAlias(existingAliases)
        aliasesDict[lang] = existingAliases
        _itemContents['aliases'] = aliasesDict
        return (_itemContents, len(existingAliases) != priorAliasCount)

    def collectEdits(itemContents_changedFields, value_field):
        # returns (itemContents, changedFields), updated per <value_field>
        #   which may be [] or [<value> {'label' or 'alias'}]
        itemContents, changedFields = itemContents_changedFields
        value, field = value_field
        pywikibot.output("collecting edit %s/%s" % value_field)
        if field == "labels":
            itemContents = updateLabels(itemContents, value)
            return (itemContents, changedFields.union(set(['labels'])))
        itemContents, newAlias = updateAliases(itemContents, value)

        return (itemContents, changedFields.union(set(['aliases'] 
                                                      if newAlias 
                                                      else [])))

    existingLabel = (itemContents['labels'][lang] 
                     if lang in itemContents['labels'] 
                     else None)


    for value, field in prefer(existingLabel, label):
        itemContents, changedFields = collectEdits(itemContents_changedFields,
                                                   (value, field))
    return (itemContents, changedFields)

def createEditSpecification (editAndClaimSpecifications):
    """
    Returns non-empty <editSpec> only if "labels" or "aliases" is in 
      <changedLabelsAndAliases>, else {}
    Where:
    <editSpec> :=  {"labels" : {<lang> : <label>}, 
                    "aliases" : {<lang> : [ <alias>, ...] }}
        directing the Wikibase wbeditentity API to assert said labels and 
        aliases

    <editAndClaimSpecifications> := {?itemContents ?changedLabelsAndAliases, 
                                     ...}
        this is the distilation of the process of parsing and interpreting the 
        contents of the infobox

    <itemContents> := {'labels' : {<lang> : <label>, ...}, 
                       'aliases' : {<lang> : [<alias>, ...], 
                        ...}, 
                       ...}
    <changedLabelsAndAliases> is subset of set(["labels", "aliases"])
        indidates whether changes were inferred for either labels or aliases
    """
    if 'changedLabelsAndAliases' not in editAndClaimSpecifications:
        return {}
    itemContents = editAndClaimSpecifications['itemContents']
    def mergeEdits(editSpec, changedField):
        # returns {"labels" : {<lang> : <label>}, 
        #          "aliases" : {<lang> : [ <alias>, ...] }}
        # per <changedField> in ("labels", "aliases")
        def selectLanguage(fieldContents):
            # returns only the part of <fieldContents> mapped to current language
            lang = pywikibot.config.mylang
            return {lang : fieldContents[lang]}
        editSpec.update({changedField 
                         : selectLanguage(itemContents[changedField])})
        return editSpec

    editSpec = {}
    for changedField in (
            editAndClaimSpecifications['changedLabelsAndAliases']):
        editSpec = mergeEdits(editSpec, changedField)
    return editSpec

def executeEditSpecification (item, editSpec):
    """
    Side-effect: makes the API call to editEntity per <editSpec>, 
      unless pywikibot.config.simulate
    Where
    <editSpec> := {"labels" : {<lang> : <label>}, 
                  "aliases" : {<lang> : [ <alias>, ...] }}
      ... the output of editSpecification(). These are new values for labels 
      and aliases for <lang>
    """

    # pywikibot.output("edit spec:%s" % editSpec)
    if not editSpec:
        return
    if not pywikibot.config.simulate:
        # raise Exception ("not ready to do pull the trigger yet")
        try:
            item.editEntity(editSpec, summary=editSpec['summary'])
        except Exception as e:
            try:
                pywikibot.output(str(e))
            except Exception as ee:
                pywikibot.output("Unprintable exception of type %s" % type(ee))
    else:
        pywikibot.output("Editing %s:%s" % (item.title(), editSpec))
        pywikibot.output("SIMULATION: not editing field")

# Claims ...
def addClaimSpec(page_parse, action_spec):
    """
    Returns <page_parse> <- {?claims}, 
    Side effect: <target> added to <claim>
    Where
    <page_parse> := {?claims ...}
    <claims> := {<pnum> : [<action_spec>, ...]
    <action_spec> := {?action ?claim ?target ...}, a field parse that 
      has been annotated with an 'action' after successfully running the 
      gauntlet of constraint checks
    """
    action_spec['claim'].setTarget(action_spec['target'])
    pnum = action_spec.get('claim').getID()
    assert action_spec.get('claim').getTarget()
    claimsDict = page_parse.get("claims", {})
    spex = claimsDict.get(pnum, [])
    claimsDict[pnum] = spex + [action_spec]
    page_parse["claims"] = claimsDict
    return page_parse

#####################
## Interpreting the supporting ontology
#####################

prefix_dict = {
    ":" : "http://naturallexicon.org/harvest/#",
    "rdfs:" : "http://www.w3.org/2000/01/rdf-schema#",
    "harvest:" : "http://naturallexicon.org/harvest/#",
    "p:" : "http://www.wikidata.org/prop/",
    "pq:" : "http://www.wikidata.org/prop/qualifier/",
    "ps:" : "http://www.wikidata.org/prop/statement/",
    "wdp:" : "https://www.wikidata.org/wiki/Property:",
    "wdt:" : "http://www.wikidata.org/prop/direct/",
    "wd:" :  "http://www.wikidata.org/entity/"
    }
def prefix (k, v):
    return "PREFIX %s <%s>" % (k, v)

CONFIG_PREFIXES = "\n".join([prefix(k, v)
                             for (k, v) in prefix_dict.items()])

prefix_re = re.compile( "|".join(prefix_dict.values()))

def strip_prefix(uri):
    """
    Returns just the name of <uri>, with any prefix in CONFIG_PREFIXES removed.
    """
    return prefix_re.sub("", uri)

P_URI_RE = re.compile(".*(P[0-9]+)$")
# ... any string that ends in a P-number

def parse_p_number(uri):
    """
    Returns P-number at the end of <uri>, or <uri> if there is no p-number
    Where
    <uri> is a URI in one of the many wikibase namespaces that can do so
    """
    raise Exception("supplanted by strip_prefix")
    m = P_URI_RE.match(uri)
    if not m:
        return uri
    return m.group(1)

def get_fields(graph, run_name):
    """
    Returns {<field>, <property>, ...} , derived from the 
      the :HarvestRun instance named by run_name
    Where
    <graph> is an RDF graph loaded from -c argument and the native
      constrained_harvest ontolology.
    <run_name> regex-matches an instance of HarvestRun in <graph>
    <field> names a field in the templates associated with <run>
    <run> regex-matches <run_name> in <graph>
    <property> := <p-number> or Label or Time, associated with <field>
    """
    q = pystache.render("""
    {{{prefixes}}}
    Select ?field ?pSpec
    Where
    {
      ?run :fieldSpec ?spec.
      Filter Regex(Str(?run), "{{run_name}}", "i")
      ?spec :field ?field;
            :property  ?propertyUri.
      Bind(Replace(Str(?propertyUri), 
                   Concat (Str(wdp:), "|", Str(wdt:), "|",  Str(:)),
                   "")
           as ?pSpec)
    }
    """, {"prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})
    
    pywikibot.output("query in get_fields:%s" % q)
    results = [[str(r['field']), str(r['pSpec'])]
               for r in graph.query(q)]
    print ("results in get_fields:%s" % results)
    result = {}
    for [field, pSpec] in results:
        result[field] = strip_prefix(pSpec) #parse_p_number(pSpec)
    return result

def get_implicits(graph, run_name):
    """
    Returns <implicits> for the harvest run  named by <run name> in <graph>
    Where
    <implicits> := {<property> : <implicit>, ...}
    <graph> is an RDF graph loaded from -c argument and the native
      constrained_harvest ontolology.
    <run_name> regex-matches an instance of HarvestRun in <graph>
    <property> is a p-number for a WD property
    <implicit> is a Q-number for some WD entity to be asserted as the object
      of a <property> assertion for an item parsed from a template for which
      no value for <property> yet exists.
    """
    q = pystache.render("""
    {{{prefixes}}}
    Select ?property ?implicit
    Where
    {
     ?run :implicitSpec ?spec.
     Filter Regex(Str(?run), "{{run_name}}", "i")
     ?spec :property ?propertyUri;
           :value  ?implicitUri.
     Bind(Replace(Str(?propertyUri), Concat(Str(wdt:), "|", Str(wdp:)), "")
          as ?property)
     Bind(Replace(Str(?implicitUri),Str(wd:), "")
          as ?implicit)

    }
    """, {"prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})
    
    pywikibot.output("query:%s" % q)
    results = [[str(r['property']), str(r['implicit'])]
               for r in graph.query(q)]
    print ("results in get_implicits:%s" % results)
    result = {}
    for [k, v] in results:
        result[strip_prefix(k)] = v
    return result

def get_field_constraints(graph, run_name):
    """
    Returns {<field>, <range>, ...} , derived from the 
      the :HarvestRun instance named by run_name in <graph>
    Where
    <graph> is an RDF graph loaded from -c argument and the native
      constrained_harvest ontolology.
    <run_name> regex-matches an instance of HarvestRun in <graph>
    <field> names a field in the templates associated with <run>
    <run> regex-matches <run_name> in <graph>
    <property> := <p-number> or Label or Time
    <range> a constraint on the range on <property>
    """
    # TODO: check for cases where there are unspecified range constraints,
    # ... and also no native constraints. Either fail or issue a warning.
    q = pystache.render("""
    {{{prefixes}}}
    Select ?field ?range
    Where
    {
      ?run :fieldSpec ?spec.
      Filter Regex(Str(?run), "{{run_name}}", "i")
      ?spec :field ?field;
        :property  ?propertyUri.
      Bind(Replace(Str(?propertyUri), 
                   Concat (Str(wdp:), "|", Str(wdt:), "|",  Str(:)),
                   "")
           as ?property)
      ?spec :range  ?rangeUri.
      Bind(Replace(Str(?rangeUri), 
                   Str(wd:),
                   "")
           as ?range)
    }
    """, {"prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})
    
    pywikibot.output("query:%s" % q)
    results = [[str(r['field']), str(r['range'])]
               for r in graph.query(q)]
    print ("results in get_field_constraints:%s" % results)
    return results

def get_property_constraints (supporting_ontology):
    """
    Returns [<normalized_binding>, ...]  for property constraints specified in <supporting_ontology>
    Where
    <supporting_ontology> is an RDF graph informed by command-line arguments.
    <normalized_binding> := (<p> <constraint> <template>)
    <p> is the p-number of a WD property
    <constraint> is the name of a constraint on <p>
    <template> is an askQueryTemplate. For which see the ontology spec.
    """
    q = """
    {{{Prefixes}}}
    Select Distinct ?predicate ?constraint ?template
    Where
    {
      ?predicate harvest:constraint ?constraint.
      Optional { ?constraint harvest:askQueryTemplate ?template. }
    }
    """
    def normalize (r):
        predicate, constraint, template = r
        return (strip_prefix(predicate),
                strip_prefix(constraint),
                str(template) if template else None)
    return [normalize(r)
            for r in supporting_ontology.query(
            pystache.render(q,
                            {"Prefixes" : CONFIG_PREFIXES}))]

def get_checkers (graph, run_name):
    """
    Returns {?fields ?properties}, keyed to checker functions per <graph> of <run_name>
    Where
    <fields> := {<field> : <checker>, ...}
    <properties> := <property> : <checker> , ...}
    <checker> :=  fn (field_parse) -> True iff <field_parse> meets constraints.
    """

    q_re = re.compile("^Q[0-9]+$")
        
    def checker_for_constraint (spec):
        # returns checker for time or q-number
        if (spec.get('constraint', None) == "NonCyclingAdminRegion"):
            return nonCyclingAdminRegion

        if spec.get('constraint', None) == "CheckForCyclesAndOtherSubsumption":
            return checkForCyclesAndOtherSubsumption

        if spec.get('template', None):
            return custom_constraint_fn(spec.get('template'))

        m = q_re.match(spec.get('constraint'))
        if m:
            return objectRangeConstraintFn("wd:" + constraint)

        #m = time_re.match(spec.get('constraint'))
        #if m:
        if spec.get('constraint', None) == "IsTimeSpec":
            return time_range_constraint_fn()

        raise Exception ("Fell through on %s in checker_for_constraint"
                         % constraint)

    field_constraints = get_field_constraints(graph, run_name)
    #{<field> : <constraint>
    fToChecker = {}
    for field, constraint in field_constraints:
        fToChecker[field] = checker_for_constraint({"constraint" :constraint})
    pToChecker = {}
    for property, constraint, template in get_property_constraints(graph):
        pToChecker[property] = checker_for_constraint(
            {"constraint" : constraint,
             "template" : template})
    result = {"fields" : fToChecker,
              "properties" : pToChecker}
    print("result in get_checkers:%s" % result)
    return result
    
    

def get_qualifier_fields (graph, run_name):
    """
    Returns {<qualifier_field> : <qualifier_spec>, ...} per <run> with <run_name> in <graph>
    WHERE
    <qualifier_field> is the name of a template field whose data should inform
      a qualifier for some <qualified_pnum>
    <qualfier_spec> := {?qualified_pnum ?qualified_field ?qualifier_pnum}
    <qualified_pnum> is the pnumber of a top-level claim to be qualified
    <qualified_field> names the field associated with <qualified_pnum>
    """
    q = pystache.render ("""
{{{Prefixes}}}
    Select ?qualifiedField ?qualifierField  ?qualifiedP ?qualifierP
    Where
    {
      ?run :fieldSpec|:implicitSpec ?spec.
      Filter Regex(Str(?run), "{{run_name}}", "i")
      ?spec 
        :property ?qualifiedP;
        :qualifier  ?qualifierSpec.
      ?qualifierSpec 
        :field ?qualifierField;
        :property ?propertyUri.
      Bind(Replace(Str(?propertyUri), 
                   Concat (Str(wdp:), "|", Str(wdt:), "|",  Str(:)),
                   "")
           as ?qualifierP)
      Optional
      {
        ?spec :field ?qualifiedField.
      }
    }

    """, {"Prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})
    pywikibot.output("qualifier_field_query:%s" % q)
    def interpret_binding(b):
        if b:
            return str(b)
    def binding_vec(r):
        return [interpret_binding(b) for b in r]
    results =  [binding_vec(r) for r in graph.query(q)]
    print ("results in get_qualfier_fields:%s" % results)
    result = {}
    for [qualifiedField, qualifierField, qualifiedP, qualifierP] in results:
        result[qualifierField] = merge(
            {"qualified_pnum" : strip_prefix(qualifiedP),
             "qualifier_pnum" : strip_prefix (qualifierP)},
            ({"qualified_field" : strip_prefix(qualifiedField)}
             if qualifiedField else {}))
    print ("result in get_qualfiers:%s" % result)
    return result
    

def get_flags(graph, run_name):
    """
    Returns {<predicated field>, <flag field>, ...} , derived from the 
      the :HarvestRun instance named by run_name
    Where
    <graph> is an RDF graph loaded from -c argument and the native
      constrained_harvest ontolology.
    <run_name> regex-matches an instance of HarvestRun in <graph>
    <predicated field> names a field in the templates associated with <run>
    <run> regex-matches <run_name> in <graph>
    <flag field> is another field in the same template on which
      <predicateded field> is predicated
    NOTE: this is  applicable, e.g. in the case where the country of a player
      specifies the player's cricket team only if the 'international' field 
      in that template is set to true
    """
    q = pystache.render("""
    {{{prefixes}}}
    Select ?predicatedField ?flagField
    Where
    {
      ?run :fieldSpec ?spec.
      Filter Regex(Str(?run), "{{run_name}}", "i")
      ?spec :field ?predicatedField;
        :flag  ?flagField.
    }
    """, {"prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})
    
    pywikibot.output("query:%s" % q)
    results = [[str(r['predicatedField']),
                str(r['flagField'])]
               for r in graph.query(q)]
    print ("results in get_flags:%s" % results)
    result = {}
    for predicated_field, flag_field in results:
        result[predicated_field] = flag_field
    return result

def get_link_templates(graph, run_name):
    """
    Returns {<field>, <link template>, ...} , derived from the 
      the :HarvestRun instance named by run_name
    Where
    <graph> is an RDF graph loaded from -c argument and the native
      constrained_harvest ontolology.
    <run_name> regex-matches an instance of HarvestRun in <graph>
    <field> names a field in the templates associated with <run>
    <run> regex-matches <run_name> in <graph>
    <link template> is a string of the form "[[ ...${value} ...]]"
      for which the value parsed from the page template will be substituted.
      e.g. 'country' parsed as 'Scotland' from a cricket player's infobox 
      might be specified as "[[${value} national cricket team]]", and rendered 
      as [[Scotland national cricket team]].
    """
    q = pystache.render("""
    {{{prefixes}}}
    Select ?field ?linkTemplate
    Where
    {
      ?run :fieldSpec ?spec.
      Filter Regex(Str(?run), "{{run_name}}", "i")
      ?spec :field ?field;
        :linkTemplate  ?linkTemplate.
    }
    """, {"prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})
    
    pywikibot.output("query:%s" % q)
    results = [[str(r['field']),
                str(r['linkTemplate'])]
               for r in graph.query(q)]
    result = {}
    for k, v in results:
        result[k] = v
    return result


#####################
# ROBOT CLASS
# Maintains state and configures the various constraints and aggregations
#####################

class ConstrainedHarvestRobot(WikidataBot):

    """A bot to add Wikidata claims, checking constraints where they are provided."""

    def __init__(self, generator, run_name, templateTitle, supporting_ontology):
        """
        Constructor 
        Args:
        <generator> := G -> [<page>...]
        <run_name> names the bot run within <supporting_ontology>.
        <templateTitle> - Name of the template to extract from each page
        <supporting_ontology> - an RDF graph consisting of 
          constrained_harvest.ttl and contents of the -c argument from 
          command line.
        Where:
        <page> is a wikipedia page containing a <template> with <templateTitle>
        """
        super(ConstrainedHarvestRobot, self).__init__()
        self.generator = pg.PreloadingGenerator(generator)
        self.templateTitle = templateTitle.replace(u'_', u' ')
        self.templateTitles = self.getTemplateSynonyms(self.templateTitle)
        self.supporting_ontology = supporting_ontology
        self.cacheSources()
        self.implicitAssertions =  get_implicits(supporting_ontology, run_name)
        self.fields = get_fields(supporting_ontology, run_name)
        self.qualifier_fields = get_qualifier_fields(supporting_ontology,
                                                     run_name)
        self.fields['_order'] = self.fields.keys()
        self.checkers = get_checkers(supporting_ontology,
                                                      run_name)
        # self.qualifiers = get_qualifiers(supporting_ontology, run_name)
        self.aggregators = get_aggregation_fns(supporting_ontology, run_name)
        self.flags = get_flags(supporting_ontology, run_name)
        self.link_templates = get_link_templates(supporting_ontology, run_name)


    def targeted_fields(self):
        """
        Returns both top-level and qualifier fields
        """
        return self.fields.keys() + self.qualifier_fields.keys()
        
    def run_uri(self):
        q = pystache.render("""
        {{{prefixes}}}
        Select ?templateUrl
        Where
        {
        ?run :template ?templateUrl.
        Filter Regex(Str(?run), "{{run_name}}", "i")
        }
        """, {"prefixes" : CONFIG_PREFIXES,
              "run_name" : run_name})
        def strvec(r):
            return [str(b) for b in r]
        [result] = [strvec(r) for r in this.supporting_ontology.query(q)]
        return result

    def getTemplateSynonyms(self, title):
        """Fetch redirects of the title, so we can check against them."""
        temp = pywikibot.Page(pywikibot.Site(), title, ns=10) 
        # ns 10 := Template pages 
        # see https://www.mediawiki.org/wiki/Manual:Namespace
        if not temp.exists():
            pywikibot.error(u'Template %s does not exist.' % temp.title())
            exit()

        # Put some output here since it can take a while
        pywikibot.output('Finding redirects...')
        if temp.isRedirectPage():
            temp = temp.getRedirectTarget()
        titles = [page.title(withNamespace=False)
                  for page in temp.getReferences(redirectsOnly=True, 
                                                 namespaces=[10],
                                                 follow_redirects=False)
        ]
        titles.append(temp.title(withNamespace=False))
        return titles



    def collectLabelSpecifications(self, page_parse, field_parse):
        """
        Returns <page_parse> <-- {?itemContents, ?changedLabelsAndAliases, ...}
        Where:
        <page_parse> is a set of annotations for the current page 
          including specifications for changes to be made to WD via the 
          API.
        <field_parse> is a set of annotations acquired for some field
          extracted from the template.
        <itemContents> := {'labels' : {<lang> : <label>, ...}, 
                           'aliases' : {<lang> : [<alias>, ...], ...}, 
                          ...} 
           per output of item.get()
        <changedLabelsAndAliases> := subset of set(["labels", "aliases"]),
          indicating which of these, if any, were changed
        """
        #pywikibot.output("field_parse in cls:%s" % field_parse)
        [value] = [field_parse[k]
                   for k in ['value']] # a singleton
        #pywikibot.output("value in cls:%s" % value)
        itemContents = page_parse['itemContents']
        changedLabelsAndAliases = (page_parse['changedLabelsAndAliases']
                                   if 'changedLabelsAndAliases' in page_parse
                                   else set([]))
        itemContents, changedLabelsAndAliases = collectLabelAndAliasEdits(
            (itemContents, changedLabelsAndAliases),
            value)
        #pywikibot.output("changed:%s" % changedLabelsAndAliases)
        page_parse.update({"itemContents" : itemContents, 
                      "changedLabelsAndAliases" : changedLabelsAndAliases
                      })
        return page_parse

    def getWikibaseClaimConstraintChecker(self, field, pnum):
        """
        Returns fn(s p o) -> True iff constraints have been met.
        """
        # {?fields ?properties}
        # <fields> := {<field> <checker>, ...}
        # <properties> := {<pnum> <checker>, ...}
        print ("field in gwccc:%s" % field)
        print ("pnum in gwccc:%s" % pnum)
        print ("checkers fields:%s" % self.checkers.get('fields', None))
        print ("checkers properties:%s" % self.checkers.get('properties', None))
        if field in self.checkers['fields']:
            pywikibot.output("matched %s in fields" % field)
            return self.checkers['fields'][field]
        if pnum in self.checkers['properties']:
            pywikibot.output("matched %s in properties" % pnum)
            return self.checkers['properties'][pnum]

        # Else we return the default checker
        def checkRangeConstraints(parse_state):
            claim, obj = (parse_state[k]
                          for k in ['claim', 'target'])
            if isinstance(obj, pywikibot.WbTime):
                return True
            predicate = claim.getID()
            def objectQ(o):
                print ("type of o in objectQ:%s" % type(o))
                # o :~ '[[wikidata:Q...]]'
                _o = str(o).replace("[[wikidata:", "")
                return _o.replace("]]", "")

            return checkNativeConstraints(predicate,
                                          objectQ(obj))
        print ("using default checker for %s/%s" % (field, pnum))
        return checkRangeConstraints
        

    def clone_claim(self, claim):
        # used with multiple qualifiers 
        """
        Returns a new claim with same P and target as <claim>
        Where
        <claim> is a claim for some assertion already parsed from a
          template.
        Note: typically this is needed in the exemplified by the following:
        A player has played on a team from 2000-2002, then again from 
        2005-2007. This has to be encoded as two separate team membership
        assertions with start and end-time qualifiers. The install_qualifiers
        aggregator function will detect this, clone the pertenent claim,
        and install both claims with a different set of date qualifers.
        """
        clone = pywikibot.Claim(self.repo, claim.getID())
        target = claim.getTarget()
        if target:
            print ("setting target in clone_claim:%s" % target)
            clone.setTarget(target)
            pywikibot.output("clone:%s" % clone)
        else:
            print ("no target in %s" % clone)
        return clone
    

    def getWikibaseClaimSpecificationAggregator(self, field, pnum):
        """
        Returns fn(page_parse, field_parse)
                -> <page_parse> <- {?claims+}
        Where
        <field> names a template parameter
        <pnum> is the name of a property
        <page_parse> := {?claims ?itemContents }
        <claims> := {<p> : [<action_spec>, ...], ...}
        <claims>+ is <claims>, modified appropriately for <value>
        <field_parse> := {?value ?claim ...} and any other annotation
          pertenent to parsing a specific line in the template.
        <value> is a WD item, time value, etc, identified as the object
          of a relation specified in the template
        <action_spec> := <field_parse> << {?action ...}
        <itemContents> := {"claims" : {<pnum> : [<action_spec>, ...], ...}
        """
        pywikibot.output("gwcsa field:%s pnum:%s" % (field, pnum))
        checker = self.getWikibaseClaimConstraintChecker(field, pnum)
        ## TODO: get fancier as use cases arise...
        resolve_qualifier_conflict=defer_to_existing_qualifiers
        def qualification_aggregator(qspec, page_parse, field_parse):
            # installs a qualifier as approp into the claim being qualified
            return install_qualifiers(
                                      page_parse, 
                                      merge(field_parse,
                                            merge(
                                             {"checker" : checker,
                                              "choose_qualified_claim" :
                                              None, #todo: define when arises
                                              "resolve_qualifier_conflict":
                                              resolve_qualifier_conflict
                                              },
                                              qspec)))     
                
        def top_level_aggregator(fn, page_parse, field_parse):
            # installs an aggregator to top-level field or p-number
            return fn(
                page_parse, 
                merge(field_parse,
                      {"checker" : checker}))



        if field in self.qualifier_fields:
            return partial(qualification_aggregator, 
                           self.qualifier_fields[field])

        aggs = self.aggregators
        # {?fields ?properties}
        # <fields> := {<field> : <constrainedAggregatorFn>, ...}
        # <qualifier_fields> : {?qualified_pnum, ?qualified_field}
        # <constrainedAggregatorFn> 
        #   := fn(page_parse, field_parse checker) # formerly ? page, item, claim, linked_item, checker) 
        #      -> page_parse << possibly with new claim added.
        # pywikibot.output("aggs:%s" % aggs)
        
        if field in aggs['fields']:
            return partial(top_level_aggregator,
                           aggs['fields'][field])

        assert pnum
        if pnum in aggs['properties']:
            return partial(top_level_aggregator,
                           aggs['properties'][pnum])
            
        def default_aggregator(page_parse, field_parse):
            return preferExistingClaim(
                page_parse,
                merge(field_parse,
                      {"checker" : checker}))
        return default_aggregator
    
    def get_wikibase_item_handlers (self, field, pnum):
        """
        Returns <interpret>, <check> 
        Where 
        <interpret> := fn(value, item, repo) -> value
        <check> :=fn(value) -> true iff <value> is valid parse
        """
        if field in self.link_templates:
            template = self.link_templates[field]
            interpret, check = standard_wikibase_item_handlers(pnum, 
                                                                self.repo,
                                                                self.site)

            def translate_value_to_link(value, item, repo):
                value = string.Template(template).substitute(
                                        value = value.strip())
                pywikibot.output("templated value:%s" % value)
                return interpret(value, item, repo)
            return (translate_value_to_link, check)
            
        return standard_wikibase_item_handlers(pnum, self.repo, self.site)


    def collectWikibaseItemClaims(self, page_parse, field_parse): 
        """
        Returns <page_parse> << {?claims, ...}, possibly modified 
          per <field> <linked item> <page> <item> and <claim>
        Where
        <claims> := {<property> : [<claimSpec>, ...], ...}
        <claimSpec> := (<action> <page>, <item>, <claim>)
        <action> is currently one of {"add", "tentative-add"}, the latter being
          simply the winner of a process deciding between a plurality of things
          to add. An action for 'delete' might be added in future
        <page> := is and instance of page.Page from which the template
          was parsed
        <item> := an instance of page.ItemPage dedicated to some Q-number, the
          subject of <claim>
        <pnum> := is a p-number

        """

        field, pnum, value, item = (field_parse[k]
                                    for k in ['field','prop','value','item'])
        interpret, check = self.get_wikibase_item_handlers(field, 
                                                           pnum)
        linked_items = interpret(value, item, self.repo)
        pywikibot.output("item:%s. linked items:%s" % (item, linked_items))
        # [<linked item> ...]
        linked_items = [linked_item 
                        for linked_item in linked_items] 
                        #if check(linked_item)]

        # spec aggregator may decide on a single spec claim per p-number
        # or allow a plurality of claims, and will also check constraints
        # per field and p-number
        specAggregator = self.getWikibaseClaimSpecificationAggregator(
            field, pnum)
        pywikibot.output("aggregator:%s" % specAggregator)
        for ordinal in range(len(linked_items)):
            linked_item = linked_items[ordinal]
            if not check(linked_item):
                continue
            # pywikibot.output("item passed to aggregator:%s" % item)     
            claim = pywikibot.Claim(self.repo, pnum)
            page_parse = specAggregator(
                page_parse,
                merge(field_parse,
                      {"ith" : ordinal,
                       "out_of" : len(linked_items),
                       "target" : linked_item,
                       "claim" : claim}))

        #pywikibot.output("page_parse:%s" % page_parse.get('claims', None))
        return page_parse


    def get_literal_handlers(self, field, pnum):
        """
        Returns (pre, post, check) possibly customized for <field> or 
          <p number>
        Where:
        <field> names a template parameter
        <p number> names a WB property
        <pre> := fn(maybe bad literal) -> good_literal
        <post> := fn(good literal) -> <checkable literal>
        <check> := fn(checkable) -> True iff <checkable literal> is appropriate
          to <field> and <p number>
        """
        # return field-specific handlers here, if any
        # default...
        return standardLiteralHandlers(pnum)

    def collectLiteralClaims (self, page_parse, field_parse):
        """
        TODO: flesh this out
        """
        pnum, field, value, page = (field_parse[k]
                                    for k in ['prop', 'field', 'value', 'page'])
        interpret, check = self.get_literal_handlers(field, pnum)

        literals = interpret(value)
        specAggregator = self.getWikibaseClaimSpecificationAggregator(
            field, pnum)
        
        for i in literals:
            literal = literals[i]
            if not check(literal):
                pywikibot.output (
                    "%s does not match constraints for field %s and property %s. Skipping..." % (literal, field, pnum))
                continue
            claim = page.Claim(pnum)
            page_parse = specAggregator(page_parse, 
                                   merge(field_parse,
                                         {"claim" : claim,
                                          "target" : literal,
                                          "ith" : i,
                                          "out_of" : len(literals)}))
        return page_parse


    def get_quantity_handlers(self, field, pnum):
        """
        TODO: flesh this out
        """
        # return field-specific handlers here, if any
        # default...
        return standard_quantity_handlers (pnum)

    def collectQuantityClaims(self, page_parse, field_parse):

        """
        Returns specAggregator(page_parse, page, item, claim, quantity)
        Where:
        <page_parse> := {?claims ?itemContents }
        <quantity> is a number
        <claims> := {<p> : [<spec>, ...], ...}
        <spec> := (<action>, <page>, <item>, <claim>), a specification to change 
          the Wikibase
        <itemContents> := {"claims" : {<pnum> : [<claim>, ...], ...}
        <claim> is an instance of pywikibot.Claim

        """
        field, pnum, value, page  = (field_parse[k]
                                     for k in ['field', 'prop', 'value', 
                                               'page'])
        interpret, check = self.get_quantity_handlers(field, pnum)
        specAggregator = self.getWikibaseClaimSpecificationAggregator(
            field, 
            pnum)

        quantities = interpret(value)
        for i in len(quantities):
            quantity = quantities[i]
            if not check(quantity):
                continue
            pywikibot.output("quantity:%s" % quantity)
            claim = page.Claim(pnum)
            claim.setTarget(quantity)
            pywikibot.output("spec aggregator for quantity:%s" 
                             % specAggregator)
            page_parse = specAggregator(page_parse, 
                                        merge (field_parse,
                                               {"claim" : claim,
                                                "target" : quantity,
                                                "ith" : i,
                                                "out_of" : len(quantities)}))

        return page_parse

    def get_url_handlers(self, field, pnum):
        # TODO: document
        # return field-specific handlers here, if any
        # default...
        return standard_url_handlers (pnum)

    def collectUrlClaims(self, page_parse, field_parse):
        # TODO: document
        field, pnum, value, page = (field_parse[k]
                                    for k in ['field', 'prop',
                                              'value','page'])
        pywikibot.output("starting url with value %s" % value)
        prop = pnum
        specAggregator = self.getWikibaseClaimSpecificationAggregator(
            field,
            prop)
        interpret, check = self.get_url_handlers(field, pnum)
        urls = interpret(value)
        for i in len(urls):
            url = urls[i]
            if not check(url):
                pywikibot.output("%s does not appear to be a URL. Skipping." % value)
                continue
            claim = page.Claim(pnum)

            page_parse = specAggregator(page_parse, 
                                        merge(field_parse,
                                              {"claim" : claim,
                                               "target" : url,
                                               "ith" : i,
                                               "out_of" : len(urls)}))

        return page_parse
        #raise Exception ("Still need to itegrate url claim %s" % value)

    def get_time_handlers(self, field, pnum):
        # TODO: document
        # place field-specific handlers here
        return standard_time_handlers(pnum)

    def collectTimeClaims(self, page_parse, parse_state):
        """
        Returns specAggregator(page_parse, <parse state> << <time spec>) 
          for each <time spec> parsed from <value>
        Where:
        <page_parse> := {?claims ?itemContents }
        <specAggregator> := fn(page_parse, page, item, claim, wbTime) -> <page_parse>,
          appropriate to <field> and <claim>
        todo: edit this docstring
        <wbTime> :=  {?.year ?.month ?.day ?.hour ?.minute ?.second ?.precision},
          an instance of pywikibot.WbTime
        <claims> := {<p> : [<spec>, ...], ...}
        <spec> := (<action>, <page>, <item>, <claim>), a specification to change 
          the Wikibase
        <itemContents> := {"claims" : {<pnum> : [<claim>, ...], ...}

        """
        
        field, time_spec, value = (parse_state[k]
                              for k in ['field', 'prop', 'value'])

        def translate_time_key(key):
            # see https://www.wikidata.org/wiki/Special:WhatLinksHere/Q18636219
            # for other options
            # pywikibot.output("key in ttk:%s" % key)
            k_v = {"at" : "P585",
                   "from" : "P580",
                   "to" : "P582"
                   }
            def lookup_field (field):
                return self.fields.get(
                    field,
                    self.qualifier_fields[field]['qualifier_pnum']).lower()
            print("field lookup in ttk:%s" % lookup_field(field))
            if lookup_field(field) == 'start' and key == 'at':
                return "P580"
            if lookup_field(field) == 'end' and key == 'at':
                return "P582"
            return k_v.get(key)
                

        specAggregator = self.getWikibaseClaimSpecificationAggregator(
            field,
            time_spec)
        interpret, check = self.get_time_handlers(field, time_spec)

        time_values = None
        try:
            time_values = interpret(value)
        except Exception as e:
            pywikibot.output ("PARSE FAILURE FOR TIME VALUE %s" % value)
            pywikibot.output(e)
            return page_parse

        # test and aggregate the time specs
        #pywikibot.output("time_values: %s" % time_values)
            
        for i in range(len(time_values)):
            def handle_time_spec(page_parse, spec):
                # spec := {?at or ?from ?to}
                if not check(spec):
                    pywikibot.output("%s did not pass the check. Skipping." 
                                     % spec)
                    return page_parse
                # Convert single-point time specifications into ranges
                # if that's what's specified...
                if time_spec.lower() == "timerange" and "at" in spec:
                    spec = {'from' : spec['at'],
                            'to' :spec['at']}
                    # pywikibot.output("new spec:%s" % spec)

                for key, value in spec.items():
                    #pywikibot.output("key in spec item loop:%s" % key)
                    pnum = translate_time_key(key)
                    #pywikibot.output("Time pnum:%s" % pnum)
                    claim = pywikibot.Claim(self.repo, pnum)
                    page_parse = specAggregator(
                        page_parse, 
                        merge(parse_state,
                              {"claim" : claim,
                               "target" : value,
                               "group" : (spec if len(time_values) > 1 
                                          else None),
                               "ith" : i,
                               "out_of" : len(time_values)}))
                return page_parse

            time_value = time_values[i]
            # pywikibot.output("time_value:%s"  % time_value)
            if type(time_value) == type([]):
                for _time_value in time_value:
                    page_parse = handle_time_spec(page_parse, _time_value)
            else:
                page_parse = handle_time_spec(page_parse, time_value)
        return page_parse

    def get_global_coordinate_handers(self, field, pnum):
        # TODO: document
        # put field- or -pnum specific handing here.
        # default...
        return standard_global_coordinate_handlers(pnum)

    def collectGlobalCoordinateClaims(self, page_parse, field_parse):
        # TODO: document
        field, pnum, value, page = (
            field_parse[k] for k in ['field', 'prop', 'value', 'page'])
        interpret, check = self.get_global_coordinate_handlers(
            field, 
            pnum)
        specAggregator = self.getWikibaseClaimSpecificationAggregator(
            field,
            pnum)
        coordinates = interpret(value)
        for i in len(coordinates): 
            coord = coordinates[i]
            if not check(coord):
                continue
            claim = page.Claim(pnum)
            claim.setTarget(coord)
            page_parse = specAggregator(
                page_parse, 
                merge(field_parse,
                      {"claim" : claim,
                       "target" : coord,
                       "ith" : i,
                       "out_of" : len(coordinates)}))
        return page_parse

    def get_commons_media_handlers(self, field, pSpec):
        # TODO: document
        return standard_commons_media_handlers(pSpec)

        
    def collectCommonsMediaClaims (self, page_parse, field_parse):
        # TODO: document
        raise Exception ("Still need to itegrate commons media claim")
        field, pnum, page, value =(field_parse[k]
                                   for k in ['prop', 'prop', 'page', 'value'])
        interpret, check = self.get_commons_media_handlers(
            field, pnum)
        images = interpret(value)
        for image in images:
            if not check(image):
                pywikibot.output(
                    '[[%s]] doesn\'t exist so I can\'t link to it'
                    % (image.title(),))
            continue
            claim = page.Claim(pnum)
            claim.setTarget(image)
        # todo: flesh this out when you're dealing with something you 
        # can test against
    def processFlag(this, page_parse, field_parse):
        """
        Returns <page_parse> << {'licensed' : {<predicated_field>, ...}}
        iff <value> is 'true'(ish)
        and <licensing_field> is in this.flags[<predicated_field>]
        Where
        <value> := <field_parse>['value']
        <licensing_field> := <parse state>['field']
        """
        [licensing_field, flag_str] = [field_parse[k]
                                       for k in ['field', 'value']]
        affirmative_regex = re.compile("true|yes", re.IGNORECASE)
        negative_regex = re.compile("false|no", re.IGNORECASE)
        for predicated_field in this.flags.keys():
            if licensing_field in this.flags[predicated_field]:
                pywikibot.output("test value:%s" % flag_str)
                m = affirmative_regex.search(flag_str)
                if not m:
                    m2 = negative_regex.match(flag_str)
                    if not m2:
                        pywikibot.output("WARNING: no handler for %s" 
                                         % flag_str)
                if m:
                    licensed = page_parse.get("licensed", set([]))
                    pywikibot.output("licensing %s" % predicated_field)
                    return merge(page_parse,
                                 {'licensed' 
                                  : licensed.union({predicated_field})})
        return page_parse
    
    def is_licensed(self, page_parse, field_parse):
        """
        Returns True iff there are no licensing issues inferable
        from self.flags. Field order should be appropriate so that
        licensing fields precede predicated fields
        """
        if len(self.flags) == 0:
            return True
        field = field_parse['field']
        if not field in self.flags:
            return True
        return 'licensed' in page_parse and field in page_parse['licensed']

    def collectClaimSpecifications(self, page_parse, field_parse):
        """
        Returns <page_parse> << {?claims}, possibly modified 
          per <field> <value> and <item>
        Where
        <claims> := {<property> : [<claimSpec>, ...], ...}
        <claimSpec> := (<action> <page>, <item>, <claim>)
        """
        # first we create a dummy claim to get the claim type
        # so we can dispatch the correct parser...

        field, prop, value = (field_parse[k]
                              for k in ["field", "prop", "value"])

        if prop.lower() == 'boolean': # Not supported by API
            # this is a flag that will license other fields
            return self.processFlag(page_parse, field_parse)

        if not self.is_licensed(page_parse, field_parse):
            pywikibot.output("%s not licensed" % field_parse['field'])
            return page_parse

        def valid_claim_prop_for(prop):
            print ("prop in vcp:%s" % prop)
            if (re.sub("harvest:", "", prop.lower())
                in ['time','timerange', 'start', 'end']):
                return "P580"
            return prop
        pywikibot.output("prop:%s" % prop)
        pywikibot.output("valid claim prop:%s" % valid_claim_prop_for(prop))
        claim = pywikibot.Claim(self.repo, valid_claim_prop_for(prop))
        
        print("about to look at type of claim with target %s" % claim.target)

        print("claim.id:%s" % claim.id)
        pywikibot.output("claim.type:'%s'" % claim.type)

        if claim.type == 'wikibase-item' :

            return self.collectWikibaseItemClaims(page_parse, 
                                                  field_parse)

        if claim.type in ('string', 'external-id'):
            return self.collectLiteralClaims(page_parse, 
                                             field_parse)

        if claim.type == 'commonsMedia':
            return self.collectCommonsMediaClaims(page_parse, 
                                                  field_parse)

        if claim.type in ['globe-coordinate']:
            return self.collectGlobalCoordinateClaims(page_parse, 
                                                      field_parse)
        if claim.type in ['url']:
            return self.collectUrlClaims(page_parse, field_parse)

        if claim.type in ['time']:
            return self.collectTimeClaims(page_parse, field_parse)

        if claim.type in ['quantity']:
            return self.collectQuantityClaims(page_parse, field_parse)

        raise Exception ("Unexpected claim type %s" % claim.type)


    def collectEditAndClaimSpecifications(self, page_parse, field_parse):
        """
        Returns <page_parse> << {?edits ?claims}
        Where:
        <page_parse> := {?itemContents ?edits ?claims}
        <field> names a field in self.fields
        <value> is a string of template data parsed from <field> in 
          some template on <page>
        <edits> := [<editSpec>, ...]
        <claims> := [<claimSpec>, ...]
        <editSpec> := {?labels ?aliases}
        <labels> := {<lang> : <label>}
        <aliases> := {<lang> : [<alias>, ...]}
        <claimSpec> := (<action>, <page>, <item>, <claim>), sufficient to drive
        """
        # coveredProperties = set([])
        #
        field, prop, value = (field_parse[k]
                              for k in ['field', 'prop', 'value'])
        # covered_properties = page_parse.get('coveredProperties', set([]))
        # if prop:
        #     covered_properties = covered_properties.union({prop})
        #     page_parse['coveredProperties'] = covered_properties
        if not value:
            return page_parse
        field = field.strip() #.lower()
        pywikibot.output("field in ceacs:%s" % field)
        value = value.strip()
        assert 'itemContents' in page_parse
        #pywikibot.output("value:%s" % value)
        if not field or not value:
            pywikibot.output("no value for %s returning unchanged" % field)
            return page_parse

        if not (field in self.targeted_fields()
                or is_implicit_field(field)):
            pywikibot.output("%s not targeted. returning unchanged" % field)
            return page_parse
        
        if prop.lower() == 'label': 
            # pywikibot.output("collecting label spec...")
            page_parse = self.collectLabelSpecifications(page_parse, 
                                                    field_parse)
            assert len(page_parse) > 0
            return page_parse

        page_parse = self.collectClaimSpecifications(page_parse, 
                                                field_parse)
        return page_parse
        

    def cover_implicit_assertions (self, page_parse, field_parse):
        """
        Implicit assertions are attached to the template spec. 
        using the harvest:implicitSpec relation
        """
        
        page, item = (field_parse[k]
                      for k in ["page", "item"])

        #pywikibot.output ("page:%s. item:%s" % (page, item))
        # pywikibot.output ("implicit assertions:%s" 
        #                   % self.implicitAssertions)
        if len(self.implicitAssertions) == 0:
            return page_parse

        def collectImplicitClaims(page_parse, (predicate, implicitValue)):
            # print("covered:%s" % page_parse.get('coveredProperties', {}))
            # if ('coveredProperties' in page_parse 
            #     and predicate in page_parse['coveredProperties']):
            #     pywikibot.output("%s covered" % predicate)
            #     return page_parse
            # # else predicate was not covered
            # pywikibot.output("%s not covered" %  predicate)
            pywikibot.output("implicit value of %s:%s" % (predicate,
                                                          implicitValue))
            # implicitClaim = pywikibot.Claim(self.repo, predicate)
            # target = pywikibot.ItemPage(self.repo, implicitValue)
            # implicitClaim.setTarget(target)
            # pywikibot.output("fresh implicit claim:%s" % implicitClaim)
            return self.collectWikibaseItemClaims(
                page_parse, 
                merge(field_parse,
                      {"field" : implicit_field(predicate),
                       "prop" : predicate,
                       "value" :implicitValue
                       })
            )
                
        for predicate, implicitValue in self.implicitAssertions.items():
            page_parse = collectImplicitClaims(
                page_parse,
                (predicate, implicitValue))

        return page_parse

        
    def executeClaimSpecification(self, spec):
        """
        Side effect: makes the API call to execute <spec>, unless 
          pywikibot.config.simulate
        Where:
        <spec> := {?action ?page ?item ?claim ?qualifiers ...}
        <action> is one of #{add, tentative-add, ...}
        """
        action, page, item, claim = (spec[k]
                                     for k in
                                     ['action', 'page', 'item', 'claim'])
        claim = spec.get('claim')
        if action in ["add", "tentative-add"]:
            assert claim.getTarget()
            try:
                pywikibot.output("Adding %s --%s--> %s" 
                                 % (spec['item'].title(),
                                    spec['prop'], 
                                    spec['target']))

                if pywikibot.config.simulate:
                    pywikibot.output ("SIMULATION:not adding claim")
                else:
                    item.addClaim(claim, summary=spec['summary'])
                # A generator might yield pages from multiple sites
                source = self.getSource(page.site)
                source.isReference = True
                if source and not pywikibot.config.simulate:
                    claim.addSource(source, bot=True)
                qualifiers = spec.get('qualifiers', [])
                for qualifier in qualifiers:
                    pywikibot.output('Adding Qualifier %s/%s'
                                     % (qualifier['claim'].getID(),
                                        qualifier['claim'].getTarget()))
                    if pywikibot.config.simulate:
                        "SIMULATION:not adding qualifier"
                    else:
                        claim.addQualifier(qualifier['claim'], bot=True, summary=spec['summary'])
                    
            except Exception as e:
                pywikibot.output("ERROR EXECUTING CLAIM SPEC %s: %s" 
                                 % (spec, str(e)))
                return
        else:
            raise Exception ("Don't yet support exection of action %s" 
                             % action)

    def parse_templates (self, page):
        """
        Returns {<field> : <value>, ...} for each targeted <field> of <template> parsed from <page> 
        Where
        <page> is a WP page
        <field> is a field in <template> specified by the user as being targeted
        <value> is the value for <field> parsed from <template> on <page>
        """
        def collectTemplateTargets (template_targets, (template, field_to_value)):
            # Returns <template_targets> << {<template target> : <field to value> }
            # Where
            # <template target> is a valid template listed in self.templateTitles
            #   (and therefore specified on the command line)
            # <field to value> := {<field> : <value>, ...}
            # <field> is a field in <template>
            # <value> is the value parsed for <field> in <template>
            # <template> is a template parsed from some WP page

            if template in template_targets:
                pywikibot.output("Template '%s' already handled. Skipping additional template of that name." % template)
                return template_targets
            try:
                template = pywikibot.Page(page.site, 
                                          template,
                                          ns=10).title(withNamespace=False)
                # ns=10 := template pages ns
            except pywikibot.exceptions.InvalidTitle:
                pywikibot.error(
                    "Failed parsing template; '%s' should be the template name."
                    % template)
                return template_targets
            #pywikibot.output  ("checking if %s is in %s" % (template, self.templateTitles))
            if template in self.templateTitles :
                # pywikibot.output("Adding %s to templateTargets" 
                #                  % field_to_value)
                template_targets[template] = field_to_value
            return template_targets

        pagetext = page.get()
        templates = textlib.extract_templates_and_params(pagetext)
        template_targets = {} # {template : {field : value} ...}
        for template in templates:
            template_targets = collectTemplateTargets(template_targets,
                                                     template)
        return template_targets.values()


    def treat_page_and_item(self, page, item):
        """
        Process a single page/item.
        Where 
        <page> is a WP page
        <item> is the corresponding Q in WD.
        """
        def get_prop(field):
            # looks up prop associated with <field>
            if field in self.fields:
                return self.fields[field]
            if field in self.qualifier_fields:
                return self.qualifier_fields[field]["qualifier_pnum"]
            raise Exception ("No prop associated with field %s" % field)
        pywikibot.output("Page at start of treat():%s/%s" % (page, type(page)))
        itemSpex = None # hoping to clear up a bug with alias carry-over
        if willstop:
            raise KeyboardInterrupt
        self.current_page = page
        itemSpex = {'itemContents': item.get()}
        # ... a nested dictionary of the data associated with <item>
        assert itemSpex
        # TODO: clarify the template parsing stuff below
        # pywikibot.output("itemSpex at start:%s" % itemSpex)

        edit_and_claim_spex = self.cover_implicit_assertions(
                itemSpex,
                {"item" : item,
                 "page" : page})

        for field_to_value in self.parse_templates(page):
            # field_to_value := {<field> : <value>, ...}
            # parsed from the specified template
            edit_and_claim_spex = itemSpex
            for field, value in field_to_value.items():
                pywikibot.output("field:%s. value:%s" % (field, value))
                print ("targeted fields:%s" % self.targeted_fields())
                if field not in self.targeted_fields():
                    continue
                edit_and_claim_spex = self.collectEditAndClaimSpecifications(
                    edit_and_claim_spex, 
                    {"field" : field,
                     "prop" : get_prop(field),
                     "value" : value,
                     "page" : page,
                     "item" : item})

            summary = ("Derived from template %s"
                       % self.templateTitle)

            ## Implement the edit and claim spex...
            #edit labels...
            editSpec = createEditSpecification(edit_and_claim_spex)
            editSpec['summary'] = summary
            executeEditSpecification(item, editSpec)
            # make claims...
            for (pnum, claimSpex) in (edit_and_claim_spex['claims'].items()
                                        if 'claims' in edit_and_claim_spex 
                                        else []):
                 for claimSpec in claimSpex:
                     claimSpec['summary'] = summary
                     self.executeClaimSpecification(claimSpec)


#######################
# ARGUMENT PARSING
# Bot run specification is done in reference to a supporting ontology
# defined and documented in constained_harvest.ttl
#######################

def get_lang_and_template_title(graph, run_name):
    """
    Returns [<lang>, <template title>], derived from the :template property of
      the :HarvestRun instance named by run_name
    Where
    <graph> is an RDF graph loaded from -c argument and the native
      constrained_harvest ontolology.
    <run_name> regex-matches an instance of HarvestRun in <graph>
    """
    # This queries for labels for 'template' that may appear in
    # the URLs for templates
    q = pystache.render("""
    {{{prefixes}}}
    Select Distinct ?template
    Where
    {
      :WikimediaTemplate rdfs:label ?templateLabelStrLang.
      Bind(Str(?templateLabelStrLang) as ?template)
    }
    """ ,
    {
        "prefixes" : CONFIG_PREFIXES
    })
    # construct a regex fragment matching 'template' in various languages
    # to insert in the next query...
    
    template_url_re = re.compile(pystache.render(
        "https://([a-z]{2}).wikipedia.org/wiki/({{templates}}):(.*)",
        {"templates" : '|'.join([str(b['template'])
                               for b in graph.query(q)])
         }))
    
    q = pystache.render("""
    {{{prefixes}}}
    Select ?templateUrl
    Where
    {
     ?run :template ?templateUrl.
     Filter Regex(Str(?run), "{{run_name}}", "i")
    }
    """, {"prefixes" : CONFIG_PREFIXES,
          "run_name" : run_name})

    pywikibot.output("query:%s" % q)
    results = [str(r['templateUrl']) for r in graph.query(q)]
    if len(results) != 1:
        raise Exception("Could not find a unique template matching run '%s' in the -c specification.")
    
    print ("results :%s" % results)
    [result] = results
    m = template_url_re.match(result)
    assert m
    return [m.group(1), m.group(3)]


def parseArgs(args):
    pywikibot.output("args in parse args:%s" % list(args))
    supporting_ontology = rdflib.Graph()
    pywikibot.output("exists?:%s"
                     % os.path.exists("scripts/constrained_harvest.ttl"))
    supporting_ontology.parse("scripts/constrained_harvest.ttl",
            format=rdf_util.guess_format("scripts/constrained_harvest.ttl"))
    pywikibot.output("graph:%s" % supporting_ontology)

    runRe = re.compile("-r:(.*)")
    def get_run_name (m):
        return m.group(1)
    configRe = re.compile("-c:(.*)")
    def get_config_graph (m):
        supporting_ontology.parse(m.group(1), 
                format=rdf_util.guess_format(m.group(1)))
        return supporting_ontology
    blacklist_regex = re.compile("^-blacklist:(.*)$")
    whitelist_regex = re.compile("^-whitelist:(.*)$")

    def read_page_title_list(m):
        path = m.group(1)
        assert os.path.exists(path)
        result = set([])
        with open(path, 'r') as instream:
            for line in instream:
                result.add(line.strip())
        return result
    
    _args = ["-family:wikipedia"]
    run_name = None
    blacklist = None
    whitelist = None
    for arg in args:
        # print("arg:%s" % arg)
        m = runRe.match(arg)
        if m:
            run_name = get_run_name(m)
        m = configRe.match(arg)
        if m:
            supporting_ontology = get_config_graph(m)
        m = blacklist_regex.match(arg)
        if m:
            blacklist=read_page_title_list(m)
        m = whitelist_regex.match(arg)
        if m:
            whitelist=read_page_title_list(m)
        else:
            _args = _args + [arg]

    [lang, template_title] = get_lang_and_template_title (supporting_ontology,
                                                          run_name)
    _args = _args + ["-template:%s" % template_title, "-lang:%s" % lang]
    pywikibot.output ("args:%s" % _args)
    # Process global args and prepare generator args parser
    local_args = pywikibot.handle_args(_args)
    # Handles global options
    # See https://www.mediawiki.org/wiki/Manual:Pywikibot/Global_Options
    pywikibot.output("local args:%s" % local_args)
    
    # Some command-line arguments initialize the generators associated
    # with pywikibot....
    gen = pg.GeneratorFactory()
    assert gen.handleArg(u"-transcludes:" + template_title)
    for arg in _args:
        if gen.handleArg(arg):
            print ("Gen handled arg %s" % arg)
    generator = gen.getCombinedGenerator()
    assert generator
    if blacklist:
        generator = (page for page in generator
                     if page.title() not in blacklist)
    if whitelist:
        generator = (page for page in generator
                     if page.title() in whitelist)
    return (generator, run_name, template_title, supporting_ontology)



def main(*args):
    pywikibot.output("args in main:%s" % list(args))

    (generator, run_name, template_title, supporting_ontology) = parseArgs(*args)
    bot = ConstrainedHarvestRobot(generator,
                                  run_name,
                                  template_title,
                                  supporting_ontology)
    
    bot.run()


###############
# AD-HOC TESTS
###############
# TODO: remove or move to something less ad-hoc.

timestrings = [
    "{{nobreak|1996<br> 1998<br> 1999 <br>2002<br> 1999-2014<br>{{nobreak|[[2001 British and Irish Lions tour to Australia|2001]], [[2005 British and Irish Lions tour to New Zealand|2005]], [[2009 British and Irish Lions tour to South Africa|2009]], [[2013 British and Irish Lions tour to Australia|2013]]}}<br>2000-2004}}",
    "<br /><br />1996-2002<br />[[1997 British Lions tour to South Africa|1997]]",
    "2000-01<br>2000-11<br/>[[2005 British and Irish Lions tour to New Zealand|2005]]<br/>2009",
    "1991-1992<br>1991-2002<br>[[1997 British Lions tour to South Africa|1997]], [[2001 British and Irish Lions tour to Australia|2001]]",
    "{{nowrap|1999<br>2000-2013<br>[[2001 British and Irish Lions tour to Australia|2001]], [[2005 British and Irish Lions tour to New Zealand|2005]], [[2009 British and Irish Lions tour to South Africa|2009]]}}",
    "1991-",
    "1991-1996",
    '1974, 1977',
    '2002 -',
    '2006 - 2014',
    '2001<br>{{nowrap|2002-2015<br>[[2005 British and Irish Lions tour to New Zealand|2005]], [[2009 British and Irish Lions tour to South Africa|2009]], [[2013 British and Irish Lions tour to Australia|2013]]}}',
    '1955-1970<br>1955-1959<br>1955-1963',
    '1987-1998<Br />1989-1997',
    '{{nowrap|2000-03, 2005-08}}<br>2005',
    '2002-13, 2015-<br />2006',
    """
{{plainlist|
* 1947-57
* 1949-56
* 1950
}}"""
    ]
    
def test_timestrings():
    for timestring in timestrings:
        p = parse_timestrings([], timestring)
        print ("PARSED:")
        print (p)
    
def test_parse_time_values():
    for timestring in timestrings:
        p = parseTimeValue(timestring)
        print ("PARSED:")
        print (p)

def test_create_time_spec():
    for timestring in [u'2001-07']:
        p = create_time_spec(timestring)
        print ("PARSED:")
        print (p)

def test_std_time_handlers():
    doit, checkit = standard_time_handlers('P580')
    #p = doit('1987, 92-94, 96<br>1998')
    p = doit('2013- <br />2016 --')
    print("PARSED:")
    print (p)

def test_args(*args):
    print("args:%s" % list(args))
    print("parse:%s" % list(parseArgs(*args)))


    
    
def test_config():
    g = rdflib.Graph()
    pywikibot.output("graph:%s" % g)
    pywikibot.output("exists?:%s"
                     % os.path.exists("scripts/constrained_harvest.ttl"))
    g.parse("scripts/constrained_harvest.ttl",
            format=rdf_util.guess_format("scripts/constrained_harvest.ttl"))
    pywikibot.output("graph:%s" % g)
    return get_property_constraints (g)

def infer_domain_and_range (g):
    """
    This is not really used right now.
    SIDE-EFFECT: <g> is updated with domain and range inferences
    Where:
    <g> is an rdflib graph.
    Note: rdflib does not appear to support an rdfs reasoner.
      domain and range are the only inferences that pertain in this code.
    """
    template = """
    {{{Prefixes}}}
    Insert 
    {
      ?x a ?class.
    }
    Where
    {
      ?s ?p ?x.
      ?p {{DR}} ?class.
    }
    """
    g.update(pystache.render(template, {"Prefixes" : CONFIG_PREFIXES,
                                        "DR": "rdfs:domain"}))
    g.update(pystache.render(template, {"Prefixes" : CONFIG_PREFIXES,
                                        "DR": "rdfs:range"}))
        
def test_aggregate():
    g = rdflib.Graph()
    pywikibot.output("graph:%s" % g)
    pywikibot.output("exists?:%s"
                     % os.path.exists("scripts/constrained_harvest.ttl"))
    g.parse("scripts/constrained_harvest.ttl",
            format=rdf_util.guess_format("scripts/constrained_harvest.ttl"))
    g.parse("scripts/constrained_harvest_examples.ttl",
            format=rdf_util.guess_format("scripts/constrained_harvest_examples.ttl"))    
    infer_domain_and_range(g)
    return get_aggregation_fns(g, "former_country")

def test_checkers():
    g = rdflib.Graph()
    pywikibot.output("graph:%s" % g)
    pywikibot.output("exists?:%s"
                     % os.path.exists("scripts/constrained_harvest.ttl"))
    g.parse("scripts/constrained_harvest.ttl",
            format=rdf_util.guess_format("scripts/constrained_harvest.ttl"))
    g.parse("scripts/constrained_harvest_examples.ttl",
            format=rdf_util.guess_format("scripts/constrained_harvest_examples.ttl"))    
    return get_checkers(g, "former_country")


if __name__ == "__main__":
    # pywikibot.output("argv going in:%s" % sys.argv)
    main(sys.argv)
    # test_args()
    # test_timestrings()
    # test_parse_time_values()
    # test_create_time_spec()
    # test_std_time_handlers()
