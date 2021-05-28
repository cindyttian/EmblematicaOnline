# import required modules / packages
import os, sys, requests, time, urllib, json, uuid, re, datetime, csv, threading, logging, html
import os.path
import shutil
from lxml import etree as ET
from html.parser import HTMLParser
from unicodedata import normalize
from datetime import timedelta
from mysql.connector import MySQLConnection

# Global Constants
BASE_VIAF_URL = 'http://www.viaf.org/viaf/AutoSuggest?query='
BASE_LC_Relators = 'http://id.loc.gov/search/?q=scheme:http://id.loc.gov/vocabulary/relators&q=aLabel:'
BASE_LC_Countries = 'http://id.loc.gov/search/?q=scheme:http://id.loc.gov/vocabulary/countries&q=aLabel:'
BASE_LC_Subjects = 'http://id.loc.gov/search/?q=scheme:http://id.loc.gov/authorities/subjects&q=aLabel:'
BASE_LC_MARCGAC = 'http://id.loc.gov/search/?q=scheme:http://id.loc.gov/vocabulary/geographicAreas&q=aLabel:'
BASE_LC_NmeSubjects = 'http://id.loc.gov/search/?q=scheme:http://id.loc.gov/authorities/names&q=aLabel:'
BASE_LC_genreSubjects = 'http://id.loc.gov/search/?q=scheme:http://id.loc.gov/authorities/genreForms&q=aLabel:'
 
transform = ET.XSLT(ET.parse('spineMods2medusaJson1August.xsl'))
transformMods2Rdf = ET.XSLT(ET.parse('spineMods2rdfJson4Aug.xsl'))
transformEmblem2Rdf = ET.XSLT(ET.parse('spineEmblem2rdfJson4Aug.xsl'))

# Global Mappings
relators = {
"creator" : "http://id.loc.gov/vocabulary/relators/cre",
"illustrator" : "http://id.loc.gov/vocabulary/relators/ill",
"collaborator" : "http://id.loc.gov/vocabulary/relators/ctb",
"clb" : "http://id.loc.gov/vocabulary/relators/ctb", 
"engr" : "http://id.loc.gov/vocabulary/relators/egr"
}

subjects = {
"emblems" : "http://id.loc.gov/authorities/subjects/sh85042693",
"emblem books, latin" : "http://id.loc.gov/authorities/subjects/sh2004006698"
}

geoAreas = {
"poland" : "http://id.loc.gov/vocabulary/geographicAreas/e-pl"
}

nmeSubjects = {
"caesar,julius" : "http://id.loc.gov/authorities/names/n79021400",
"charles, vi, holy roman emperor, 1685-1740" : "http://id.loc.gov/authorities/names/n84000727",
"leopold, archduke of austria, 1716-1716" : "http://id.loc.gov/authorities/names/no2001061965"

}

genreSubjects = {
"poetry" : "http://id.loc.gov/authorities/genreForms/gf2014026481"
}


oldPaths = {}
# open the csv, iterate through it and populate the dictionary
with open('AllBooks-v1.csv', 'r', newline='') as myCsvFile:
	myCsvRdr = csv.DictReader(myCsvFile, delimiter=',', fieldnames=['bookId', 'bookLocation'])	
	for myRow in myCsvRdr :
		oldPaths[myRow['bookId']] = myRow['bookLocation']	
	
# Look through the result from an API call that returned 200 to see if it is just an error message.
# Returns 1 for an error and 0 for no error.
def checkForError(error_case,result,url):
	if 'viaf.org' in url:
		return result.content.find(error_case) != 0
	else:
		return result.content.find(error_case) == -1

# getRequest Handles calls out to the three services we use, checks returned data to make sure it is present
#	and in the right format. If there is an error or timeout, this handles the error. If a response
#	is 403 or 404, we give up. If we get a 200 response but it contains an error message about the
#	service rather than the content we want, we retry. We keep retrying the query every 6 seconds to 
#	avoid overwhelming the service until we get a proper response.
# check for names / subjects in viaf.org  
def getRequest(url,expectJSON):
	local_start_time = datetime.datetime.now().time()

	if 'viaf.org' in url:
		try:
			h = HTMLParser()
			splitpoint = url.find('?query=')+7
			url = url[:splitpoint] + html.unescape(url[splitpoint:])
			logging.debug(url)
		except UnicodeDecodeError:
			h = HTMLParser.HTMLParser()
			splitpoint = url.find('?query=')+7
			url = url[:splitpoint] + html.unescape(url[splitpoint:].decode('utf-8'))
			logging.debug(url)
		except:
			raise

		error_case = b'<'
	else:
		error_case = b'<title>Temporarily out of service</title>'

	logging.debug(url)
	try:
		result = requests.get(url,timeout=60)
		if expectJSON:
			check_json = result.json()
	except (requests.exceptions.ConnectionError, requests.exceptions.Timeout, ValueError) as e:
		try:
			if result:
				logging.debug(result.status_code)
		except:
			result = BrokenResponse()

	if result.status_code == 403 or result.status_code == 404:
		local_end_time = datetime.datetime.now().time()
		duration = datetime.datetime.combine(datetime.date.min,local_end_time)-datetime.datetime.combine(datetime.date.min,local_start_time)
		logging.debug("Nada")
		return None

	logging.debug(url)
	logging.debug(result.content)
	try:
		if result.status_code == 200 and checkForError(error_case,result,url):
			retry = False
		else:
			retry = True
	except:
		retry = True

	logging.debug("Retrying")

	while retry:
		logging.debug("Retrying " + url)
		logging.debug(result.status_code)
		time.sleep(6)
		try:
			result = requests.get(url,timeout=60)
			if expectJSON:
				check_json = result.json()
		except (requests.exceptions.ConnectionError, requests.exceptions.Timeout, ValueError) as e:
			try:
				if result:
					logging.debug(result.status_code)
			except:
				result = BrokenResponse()

		try:
			if result.status_code == 200 and checkForError(error_case,result,url):
				retry = False
		except:
			pass

	logging.debug("Got result")
	logging.debug(result.content)
	logging.debug(result.content.find(error_case))
	local_end_time = datetime.datetime.now().time()
	duration = datetime.datetime.combine(datetime.date.min,local_end_time)-datetime.datetime.combine(datetime.date.min,local_start_time)
	return result

# parse the spine or mods XML and enrich with valueURIs
# Creates new folder structure for the book (emulates Medusa structure)
# At end of this function we transform to get Medusa-json, rdf for book & rdf for emblems 
def parseXML(spine, destinationDirectory, fqDestinationDirectory, sourceDirectory): 

	# instantiate root of retrieved XML content (spine) as an ET Element (root)
    #   then instantiate an ET tree object from the root Element
	root = ET.fromstring(spine)
	tree1 = ET.ElementTree(root)
	
	# save the original mods or spine XML in supplementary folder
	#    Use presence / absence of bibliosDesc and mods element to help determine file name
	if len(tree1.xpath('//e:biblioDesc', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'}) ) > 0:
		fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'_spine_orig.xml'
		tree = ET.ElementTree(tree1.xpath('//e:biblioDesc', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})[0])
	elif len(tree1.xpath('//m:mods', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'}) ) > 0 :
		fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'_mods_orig.xml'
		tree = ET.ElementTree(tree1.xpath('//m:mods', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})[0])
	else :
		fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'_orig.xml'
		tree = tree1
	tree.write(fleNme)
	
	# update (overwrite as necessary) the mods schema location and version number to mods 3.7
	#    note need to specify mods schema location before setting spine schema location since spine schema imports mods 3.4, albeit using generic ver. 3 namespace URL
	biblioD = tree.xpath('//e:biblioDesc', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	for bd in biblioD:
		#print('hello')
		bd.attrib['{http://www.w3.org/2001/XMLSchema-instance}schemaLocation'] = "http://www.loc.gov/mods/v3 http://www.loc.gov/standards/mods/mods.xsd http://diglib.hab.de/rules/schema/emblem http://diglib.hab.de/rules/schema/emblem/emblem-1-2.xsd"

	modsR =	tree.xpath('//m:mods', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	for mr in modsR:
		mr.attrib['{http://www.w3.org/2001/XMLSchema-instance}schemaLocation'] = "http://www.loc.gov/mods/v3 http://www.loc.gov/standards/mods/mods.xsd"
		mr.attrib['version'] = '3.7'
		
	# update [full resolution] emblem href URLs (those pointing to images stored on UIUC emblemImages server) consistent with planned relocation
	emblems = tree.xpath("//e:emblem[@x:href]", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'x': 'http://www.w3.org/1999/xlink'})
	for emblem in emblems :
		aValue = emblem.attrib['{http://www.w3.org/1999/xlink}href'].replace(".grainger.", ".library.").replace("JP2Processed", "preservation")
		emblem.attrib['{http://www.w3.org/1999/xlink}href'] = aValue
    
	picturas = tree.xpath("//e:emblem/e:pictura[@x:href]", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'x': 'http://www.w3.org/1999/xlink'})
	for pictura in picturas:
		picturaRawUrl = pictura.xpath("@x:href", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'x': 'http://www.w3.org/1999/xlink'})[0]
		
		if picturaRawUrl.find("djatoka.grainger.illinois.edu") != -1 :
			picturaURL = "http://emblemimages.library.illinois.edu:8080/cantaloupe-4.1.4/iiif/2/"
			picturaFile = picturaRawUrl.partition("rft_id=http://emblemimages.grainger.illinois.edu/")[2].partition(".jp2")[0] + ".jp2"
			picturaURL = picturaURL+picturaFile.replace('JP2Processed', 'preservation').replace('/', '%2F')
			picturaRegion = picturaRawUrl.partition('svc.region=' )[2].split(',')
			picturaURL = picturaURL+'/'+picturaRegion[1]+','+picturaRegion[0]+','+picturaRegion[3]+','+picturaRegion[2]+'/full/0/default.jpg'
			
			pictura.attrib['{http://www.w3.org/1999/xlink}href'] = picturaURL
			# for pictura master stored on emblemImages, copy pictura jp2 file into preservation 
			if picturaRawUrl.find("emblemimages.grainger.illinois.edu") != -1 :
				destPic = fqDestinationDirectory + '\\preservation\\' + picturaFile.split("/")[-1]					
				sourcePic = sourceDirectory+ '\\JP2Processed\\' + picturaFile.split("/")[-1]
				if os.path.exists(sourcePic) and os.path.isfile(sourcePic) :
					shutil.copy2( sourcePic, destPic )					
					

	# adds valueURI for first languageTerm (in each language node) of type code by concatenating code value with id.loc.gov
	#   assumes all language codes are either iso639-1 (2 characters) or iso639-2 (3 characters)
	#	languageTerms of type code that already have a valueURI attribute are ignored
	#	languageTerms of type code that have code values not 2 or 3 characters in length are ignored
	langs = tree.xpath('//m:mods/m:language', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	for lang in langs :
		langTerm = lang.xpath("m:languageTerm[@type='code']", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
		if len(langTerm) > 0:
			if langTerm[0].get('valueURI') is None:
				ltS = langTerm[0].text
				if len(ltS) == 3:
					langTerm[0].attrib['authorityURI'] = "http://id.loc.gov/"
					langTerm[0].attrib['valueURI'] = "http://id.loc.gov/vocabulary/iso639-2/" + ltS
				elif len(ltS) == 2:
					langTerm[0].attrib['authorityURI'] = "http://id.loc.gov/"
					langTerm[0].attrib['valueURI'] = "http://id.loc.gov/vocabulary/iso639-1/" + ltS

	# adds valueURI for first placeTerm (in each place node) of authority='marccountry' by concatenating placeTerm text value with id.loc.gov
	#	placeTerms of authority='marccountry' that already have a valueURI attribute are ignored
	places = tree.xpath('//m:mods/m:originInfo/m:place', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	for place in places :
		placeTerm = place.xpath("m:placeTerm[@authority='marccountry']", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
		if len(placeTerm) > 0:
			if placeTerm[0].get('valueURI') is None:
					placeText = placeTerm[0].text.lower().replace(".", " ").strip()
					placeURI = "http://id.loc.gov/vocabulary/countries/"+placeText
					placeTerm[0].attrib['authorityURI'] = "http://id.loc.gov/" 
					placeTerm[0].attrib['valueURI'] = placeURI						
					
	
	Subject = tree.xpath('//m:mods/m:subject[@authority="lcsh"]', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	with open(destinationDirectory+'.csv', 'w', newline='') as t:
		fieldnames = ['bookTitle', 'termQueried', 'numberofResult', 'valueURI']
		thewriter = csv.DictWriter(t, fieldnames=fieldnames)						
		thewriter.writeheader()
		if len(Subject) > 0 :
			for sub in Subject:
				comSubMatchCount = 0
				if len(sub) == 5:
					subText = sub[0].text.lower().replace(".", " ").strip() + '--' + sub[1].text.lower().replace(".", " ").strip() + '--' + sub[2].text.lower().replace(".", " ").strip() + sub[3].text.lower().replace(".", " ").strip() + sub[4].text.lower().replace(".", " ").strip()
				elif len(sub) == 4:
					subText = sub[0].text.lower().replace(".", " ").strip() + '--' + sub[1].text.lower().replace(".", " ").strip() + '--' + sub[2].text.lower().replace(".", " ").strip() + sub[3].text.lower().replace(".", " ").strip()
				elif len(sub) == 3:
					subText = sub[0].text.lower().replace(".", " ").strip() + '--' + sub[1].text.lower().replace(".", " ").strip() + '--' + sub[2].text.lower().replace(".", " ").strip()
				elif len(sub) == 2:
					subText = sub[0].text.lower().replace(".", " ").strip() + '--' + sub[1].text.lower().replace(".", " ").strip() 
				elif len(sub) == 1:
					subText = sub[0].text.lower().replace(".", " ").strip()          
						
				lc_url = BASE_LC_Subjects + '%22'+subText+'%22'
				rslt_tree = ET.HTML(getRequest(lc_url, False).content)
				rslt_trs = rslt_tree.xpath("//table[@class='id-std']/tbody/tr")
				rslt_tbody = rslt_tree.xpath("//table[@class='id-std']/tbody[@class='tbody-group']")
				# only add valueURI if a single subject record is returned
				if len(rslt_tbody) == 1 :	
					sub.attrib['authorityURI'] = "http://id.loc.gov/" 
					sub.attrib['valueURI'] = "http://id.loc.gov"+rslt_trs[0].xpath("./td/a[@title='Click to view record']/@href")[0]	
					comSubMatchCount = 1
				else:
					comSubMatchCount = 0
					
				thewriter.writerow({'bookTitle' : fqDestinationDirectory+'comSub', 'termQueried' : subText, 'numberofResult': comSubMatchCount})		
					
				# If len(sub) == 1, don't run the follows to avoid duplicated uri.							
				if len(sub) > 1:
					# if sub.get('valueURI') is None: 		
					# process each subject of authority=lcsh that includes a <topic> child, and look for matches to <topic> value in LCSH
					# ignore <topic> nodes that already have a valueURI
					#   1st guess valueURI from <topic> value,
					#   if not, check if <topic> value is itself a valueURI,
					#   if not, search for exact match to <topic> value in LCSH			
					subjectTerm = sub.xpath('m:topic', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
					
					if len(subjectTerm) > 0 :
						for idx, sT in enumerate(subjectTerm):
							subMatchCount = 0
							if subjectTerm[idx].get('valueURI') is None:
								subjectText = subjectTerm[idx].text.lower().replace(".", " ").strip()
								subjectURI = "http://id.loc.gov/authorities/subject/"+subjectText
								
								if subjectText in subjects.keys():
									subjectTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
									subjectTerm[idx].attrib['valueURI'] = subjects[subjectText]	
									subMatchCount = 1
								elif subjectURI in subjects.values() :
									subjectTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
									subjectTerm[idx].attrib['valueURI'] = subjectURI
									subMatchCount = 1
								else :
									lc_url = BASE_LC_Subjects + '%22'+subjectText+'%22'
									print(lc_url)
									rslt_tree = ET.HTML(getRequest(lc_url, False).content)
									rslt_trs = rslt_tree.xpath("//table[@class='id-std']/tbody/tr")
									if len(rslt_trs) > 0:
										print("match")
										subjectTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
										subjectTerm[idx].attrib['valueURI'] = "http://id.loc.gov"+rslt_trs[0].xpath("./td/a[@title='Click to view record']/@href")[0]
										subMatchCount = 1
							else:
								subjectText = "valueURI already present."
											
							thewriter.writerow({'bookTitle' : fqDestinationDirectory+'sub', 'termQueried' : subjectText, 'numberofResult': subMatchCount})	
							
							
								
					# process each subject of authority=lcsh that includes a <geographic> child, and look for matches to <geographic> value in LCSH
					geoTerm = sub.xpath('m:geographic', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
					if len(subjectTerm) > 0 :
						for idx, gA in enumerate(geoTerm):
							geoSubMatchCount = 0
							if geoTerm[idx].get('valueURI') is None:
								geoText = geoTerm[idx].text.lower().replace(".", " ").strip()
								geoURI = "http://id.loc.gov/vocabulary/geographicAreas/"+geoText
								if geoText in geoAreas.keys():
									geoTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
									geoTerm[idx].attrib['valueURI'] = geoAreas[geoText]	
									geoSubMatchCount = 1
								elif geoURI in geoAreas.values() :
									geoTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
									geoTerm[idx].attrib['valueURI'] = geoURI
									geoSubMatchCount = 1
									
								else :
									geo_url = BASE_LC_MARCGAC + '%22'+geoText+'%22'
									rslt_tree = ET.HTML(getRequest(geo_url, False).content)
									rslt_trs = rslt_tree.xpath("//table[@class='id-std']/tbody/tr")
									if len(rslt_trs) > 0:
										geoTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
										geoTerm[idx].attrib['valueURI'] = "http://id.loc.gov"+rslt_trs[0].xpath("./td/a[@title='Click to view record']/@href")[0]
										geoSubMatchCount = 1	
										
							thewriter.writerow({'bookTitle' : fqDestinationDirectory+'geoSub', 'termQueried' : geoText, 'numberofResult': geoSubMatchCount})
							
					genreTerm = sub.xpath('m:genre', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
					if len(genreTerm) > 0 :
						for idx, genre in enumerate(genreTerm):
							gnrSubMatchCount = 0
							if genreTerm[idx].get('valueURI') is None:
								genreText = genreTerm[idx].text.lower().replace(".", " ").strip()
								if genreText in genreSubjects.keys():
									genreTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
									genreTerm[idx].attrib['valueURI'] = genreSubjects[genreText]
									gnrSubMatchCount = 1
								else :
									genre_url = BASE_LC_genreSubjects + '%22'+genreText+'%22'
									rslt_tree = ET.HTML(getRequest(genre_url, False).content)
									rslt_trs = rslt_tree.xpath("//table[@class='id-std']/tbody/tr")
									if len(rslt_trs) > 0:
										genreTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
										genreTerm[idx].attrib['valueURI'] = "http://id.loc.gov"+rslt_trs[0].xpath("./td/a[@title='Click to view record']/@href")[0]
										gnrSubMatchCount = 1
										
							thewriter.writerow({'bookTitle' : fqDestinationDirectory+'gnrSub', 'termQueried' : genreText, 'numberofResult': gnrSubMatchCount})
                                        
                # process each subject of authority=lcsh that includes a <name> child, and look for matches to <namePart> value in LCSH
                # <name> child stands alone within <subject> (i.e. len(sub) == 1), so this node needs to be indented back, and we can append authorityURI and valueURI directly to sub
				nmeSub = sub.xpath('m:name', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})			
				if len(nmeSub) > 0 :										
					for idx, nme in enumerate(nmeSub):
						nmeSubMatchCount = 0
						if nmeSub[idx].get('valueURI') is None:		
							nmeParts = nme.xpath('m:namePart', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})							
							if len(nmeParts) == 3:							
								nmeText = nmeParts[1].text.lower().replace(".", " ").strip() + ',' + ' ' + nmeParts[0].text.lower().replace(".", " ").strip() + ',' + ' ' + nmeParts[2].text.lower().replace(".", " ").strip()
							elif len(nmeParts) == 2:							
								nmeText = nmeParts[0].text.lower().replace(".", " ").strip() + ',' + ' ' + nmeParts[1].text.lower().replace(".", " ").strip() 
							elif len(nmeParts) == 1:							
								nmeText = nmeParts[0].text.lower().replace(".", " ").strip() 
							if nmeText in nmeSubjects.keys():
								sub.attrib['authorityURI'] = "http://id.loc.gov/" 
								sub.attrib['valueURI'] = nmeSubjects[nmeText]	
								nmeSubMarchCount = 1
							else :
								nme_url = BASE_LC_NmeSubjects + '%22'+nmeText+'%22'
								rslt_tree = ET.HTML(getRequest(nme_url, False).content)
								rslt_trs = rslt_tree.xpath("//table[@class='id-std']/tbody/tr")
								if len(rslt_trs) > 0:
									sub.attrib['authorityURI'] = "http://id.loc.gov/" 
									sub.attrib['valueURI'] = "http://id.loc.gov"+rslt_trs[0].xpath("./td/a[@title='Click to view record']/@href")[0]
									nmeSubMarchCount = 1	
									
						thewriter.writerow({'bookTitle' : fqDestinationDirectory+'nmeSub', 'termQueried' : nmeText, 'numberofResult': nmeSubMatchCount})
						
	# process each name node to add viaf and role valueURIs
	# 	Ignore if valueURI already present
	#   use displayForm if present to search VIAF
	#   	otherwise concatenate namePart[0]+namePart[1] (if both present)
	#		otherwise just take namePart[0] (if present)
	#		otherwise if no namePart[0], do not search for viaf url
	#   strip out parens characters since VIAF api doesn't seem to like
	#   assume json response
	nmes = tree.xpath('//m:mods/m:name', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	#with open(destinationDirectory+'.csv', 'w', newline='') as t:
		#fieldnames = ['bookTitle', 'termQueried', 'numberofResult', 'valueURI']
		#thewriter = csv.DictWriter(t, fieldnames=fieldnames)						
		#thewriter.writeheader()
		
	for nme in nmes :
		matchCount = 0
		if nme.get('valueURI') is None :
			nmeParts = nme.xpath('m:namePart', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
			df = nme.xpath('m:displayForm', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
			dfCurrent = False
			if len(df) == 1:
				nmePart = df[0].text
				dfCurrent = True
			elif len(nmeParts) == 2:
				nmePart=nmeParts[0].text+', '+nmeParts[1].text
			elif len(nmeParts) == 1:
				nmePart=nmeParts[0].text
			else :
				nmePart = "No namePart provided."
			if nmePart != "No namePart provided.":
				nmePart = nmePart.replace("(", "")
				nmePart = nmePart.replace(")", "")
				viaf_url = BASE_VIAF_URL + nmePart
				rslt = getRequest(viaf_url, True)		
				myNmeJ = json.loads(rslt.content.decode('utf-8'))
				if myNmeJ['result'] is not None:
					# only add valueURI if a single VIAF record (result.item) of type personal or corporate is returned
					personalCnt = 0
					for rTerm in myNmeJ['result']: 
						if rTerm['nametype'] == 'personal' or rTerm['nametype'] == 'corporate' :
							personalCnt += 1
							displayForm = rTerm['displayForm']
							viafid = 'http://viaf.org/viaf/' + rTerm['viafid']
					# If just 1 match of type personal or corporate, add authorityURI and valueURI and replace or add displayForm 
					if personalCnt == 1: 
						matchCount = 1
						nme.attrib['authorityURI'] = 'http://viaf.org'
						nme.attrib['valueURI'] = viafid
						if dfCurrent :
							# Because name parent of existing displayForm did not include a valueURI, we will overwrite displayForm with VIAF value
							df[0].text = displayForm
						else :
							df = ET.SubElement(nme, '{http://www.loc.gov/mods/v3}displayForm', )
							df.text = displayForm
					else :
						matchCount = len(myNmeJ['result'])

				else :
					matchCount = 0
	
			#thewriter.writerow({'bookTitle' : fqDestinationDirectory, 'termQueried' : nmePart, 'numberofResult': matchCount})
		else :
			nmeParts = nme.xpath('m:namePart', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
			df = nme.xpath('m:displayForm', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
			dfCurrent = False
			if len(df) == 1:
				nmePart = df[0].text
				dfCurrent = True
			elif len(nmeParts) == 2:
				nmePart=nmeParts[0].text+', '+nmeParts[1].text
			elif len(nmeParts) == 1:
				nmePart=nmeParts[0].text
			else :
				nmePart = "No namePart provided."
			if nmePart != "No namePart provided.":
				nmePart = nmePart.replace("(", "")
				nmePart = nmePart.replace(")", "")
			valueURI = nme.get('valueURI')
			#thewriter.writerow({'bookTitle' : fqDestinationDirectory, 'termQueried' : nmePart, 'numberofResult': 'valueURI present in original XML', 'valueURI': valueURI})
				
	
			# Now check each roleTerm to see if you have a value that maps to a URL or if you can find a match on id.loc.gov
			# 	Note, this is template for hybrid dictionary plus online lookup
			#   Ignore any roleTerm that already has a valueURI in our data dictionary
			#    If not, search id.loc.gov for *exact* match to a MARC relator role
		roleTerm = nme.xpath('m:role/m:roleTerm', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
		if len(roleTerm) > 0 :
			for idx, rT in enumerate(roleTerm):
				if roleTerm[idx].get('valueURI') is None:
					roleText = roleTerm[idx].text.lower().replace(".", " ").strip()
					roleURI = "http://id.loc.gov/vocabulary/relators/"+roleText
					if roleText in relators.keys() :
						roleTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
						roleTerm[idx].attrib['valueURI'] = relators[roleText]	
					elif roleURI in relators.values() :
						roleTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
						roleTerm[idx].attrib['valueURI'] = roleURI						
					else :
						lc_url = BASE_LC_Relators + '%22'+roleText+'%22'
						rslt_tree = ET.HTML(getRequest(lc_url, False).content)
						rslt_trs = rslt_tree.xpath("//table[@class='id-std']/tbody/tr")
						if len(rslt_trs) > 0:
							roleTerm[idx].attrib['authorityURI'] = "http://id.loc.gov/" 
							roleTerm[idx].attrib['valueURI'] = "http://id.loc.gov"+rslt_trs[0].xpath("./td/a[@title='Click to view record']/@href")[0]

	# now save the XML tree as enriched spine or mods file
	if len(tree.xpath('//e:biblioDesc', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'}) ) > 0:
		fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'_spine.xml'
	elif len(tree.xpath('//m:mods', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'}) ) > 0 :
		fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'_mods.xml'
	else :
		fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'.xml'
	tree.write(fleNme)

	# transform the XML tree for the book to 'Medusa'-like json
	result = transform(tree)
	fleNme = fqDestinationDirectory+'\\'+destinationDirectory+'.json'
	with open(fleNme, 'wb') as f:
		f.write(result)

	# transform the XML tree for the book to schema.org json-ld
	bookFldr = ET.XSLT.strparam(destinationDirectory)
	result = transformMods2Rdf(tree, docName=bookFldr)
	fleNme = fqDestinationDirectory+'\\supplementary\\'+destinationDirectory+'_rdf.json'
	with open(fleNme, 'wb') as f:
		f.write(result)
		
#	Now we need to create rdf for each emblem
#	Start by getting node list of all the emblems (if any) in the [spine] XML metadata file
	emblems = tree.xpath('//e:emblem', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})

#	emblemTree = ET.ElementTree(emblems[3])
#	emblemTree.write("singleEmblem.xml")

# 	generate dateCreated param needed for emblem transform - same for each emblem in this book - use mods:dateIssued
	dateIssued=tree.xpath("//m:mods/m:originInfo/m:dateIssued[@encoding='marc' or @encoding='iso8601']", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	dateIssued2=tree.xpath("//m:mods/m:originInfo/m:dateIssued", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
	
	if len(dateIssued) > 0:
		dateIssuedFromMods= ET.XSLT.strparam(dateIssued[0].text)
	elif len(dateIssued2) > 0:
		dateIssuedFromMods= ET.XSLT.strparam(dateIssued2[0].text)	
	else:
		dateIssuedFromMods= ET.XSLT.strparam(" ")
	
#	Create tree for each emblem and get emblemId (from globalID) 
#		emblemId will be used to save xml and rdf file and will (separately) be used (required) by xslt that transforms emblem metadata to rdf
	for emblem in emblems:
		emblemTree = ET.ElementTree(emblem)
		emblemId = emblemTree.xpath('substring-after(/e:emblem/@globalID,"EmblemRegistry:")', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
		emblem2Id = emblemTree.xpath('string(/e:emblem/@xml:id)', namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'm': 'http://www.loc.gov/mods/v3'})
		
		if len(emblemId) > 0 :

			fleNme = fqDestinationDirectory+'\\emblematica\\emblem'+emblemId[1:]+'.xml'
			emblemTree.write(fleNme)

			
			sourceEmbThumb = sourceDirectory + '\\JPGthumbnail\\emblem\\' + emblemId + '.jpg'
			source2EmbThumb = sourceDirectory + '\\JPGthumbnail\\emblem\\' + emblem2Id + '.jpg'
			destEmbThumb = fqDestinationDirectory + '\\_access\\emblem\\' + emblemId + '.jpg'
			if os.path.exists(sourceEmbThumb) and os.path.isfile(sourceEmbThumb) :
				shutil.copy2( sourceEmbThumb, destEmbThumb )
			elif os.path.exists(source2EmbThumb) and os.path.isfile(source2EmbThumb) :
				shutil.copy2( source2EmbThumb, destEmbThumb )
			
			sourcePicThumb = sourceDirectory + '\\JPGthumbnail\\pictura\\' + emblemId + '.jpg'
			source2PicThumb = sourceDirectory + '\\JPGthumbnail\\pictura\\' + emblem2Id + '.jpg'
			destPicThumb = fqDestinationDirectory + '\\_access\\pictura\\' + emblemId + '.jpg'
			if os.path.exists(sourcePicThumb) and os.path.isfile(sourcePicThumb) :
				shutil.copy2( sourcePicThumb, destPicThumb )
			elif os.path.exists(source2PicThumb) and os.path.isfile(source2PicThumb) :
				shutil.copy2( source2PicThumb, destPicThumb )

#			Another param for the transform - For each pictura saved on uiuc server, update url from djatoka to cantaloupe
			picturaRawUrl = emblemTree.xpath("string(/e:emblem/e:pictura/@xlink:href)", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'xlink': 'http://www.w3.org/1999/xlink'})
			picturaURL = ET.XSLT.strparam(picturaRawUrl)

			# Lastly we need to generate a param containing list of individual page images that comprise the emblem
			# Note - by design only checking UIUC, Duke and Getty for stitched image files (all of which will be on emblemImages)
			#   check if emblem master same as used for destPic / sourcePic, in which case you can skip that one multi-page version of emblem jp2.
			stitchedUrl = emblemTree.xpath("string(/e:emblem/@xlink:href)", namespaces={'e': 'http://diglib.hab.de/rules/schema/emblem', 'xlink': 'http://www.w3.org/1999/xlink'})
			emblemPageImageList = ET.XSLT.strparam(" ")
			if stitchedUrl.find("emblemimages.library.illinois.edu") != -1:
				stitchedFile = stitchedUrl.rsplit('/', 1)[1]
				# For emblem masters stored on emblemImages, copy emblem jp2 file in preservation
				destEmb = fqDestinationDirectory + '\\preservation\\' + stitchedFile
				sourceEmb = sourceDirectory + '\\JP2Processed\\' + stitchedFile
				
				#if destEmb != destPic and os.path.exists(sourceEmb) and os.path.isfile(sourceEmb):
				if os.path.exists(sourceEmb) and os.path.isfile(sourceEmb):
					shutil.copy2( sourceEmb, destEmb)
				
				myFrag2 = stitchedFile.rpartition('_')
				if myFrag2[2].find("-") != -1 :
					myFrag3 = myFrag2[2].split('.')[0].split('-', 1)
					max = int(myFrag3[1])
					min = int(myFrag3[0])
					imageList = ""
					for x in range(max-min+1):
						pg = myFrag2[0] + '_' + str(min+x).rjust(4, '0') + '.jp2'
						#   TODO: for stitched, copy each individual page image file into preservation....
					
						destEmb = fqDestinationDirectory + '\\preservation\\' + pg
						sourceEmb = sourceDirectory + '\\JP2Processed\\' + pg
						
						if os.path.exists(sourceEmb) and os.path.isfile(sourceEmb):
							shutil.copy2( sourceEmb, destEmb)
							
						imageList = imageList + pg + ' |'
					
					emblemPageImageList = ET.XSLT.strparam(imageList)
					
			
			# Finally we're ready to generate emblem RDF via transform
			result = transformEmblem2Rdf(emblemTree, docName=bookFldr, dateCreated=dateIssuedFromMods, picturaURL=picturaURL, emblemPageImageList=emblemPageImageList )
			fleNme = fqDestinationDirectory+'\\supplementary\\'+emblemId+'_rdf.json'
			with open(fleNme, 'wb') as f:
				f.write(result)
	
	return;

# iterate through the urls 
# build folder structure 
# enrich mods / spine book descriptions with urls (viaf, id.loc.gov, iconclass)
# save enriched mods / spine to supplementry folder
# copy image files - still to do!
# run appropriate xsl to create rdf and medusa-like metadata
# save metadata and rdf

with open('myList20Oct.json', 'r') as fle:
	myList = json.load(fle)
	
myUrls = myList['urlList']
dirPrefix = "E:\\emblemimages-wwwroot\\"
	
for eachUrl in myUrls :
	print(eachUrl)
	
	if eachUrl.find('HABVols') == -1 :
		dirNme = eachUrl.split("/")[-1].split(".xml")[0]
	else :
		dirNme = eachUrl.split("/")[-2]
		
	fqDirNme = dirPrefix+dirNme	
	print (fqDirNme)
	
	if not os.path.isdir(fqDirNme) : 
		os.mkdir(fqDirNme)
	if not os.path.isdir(fqDirNme+'\supplementary') : 
		os.mkdir(fqDirNme+'\\supplementary')
	if not os.path.isdir(fqDirNme+'\preservation') : 
		os.mkdir(fqDirNme+'\\preservation')
	if not os.path.isdir(fqDirNme+'\emblematica') : 
		os.mkdir(fqDirNme+'\\emblematica')
	if not os.path.isdir(fqDirNme+'\_access') : 
		os.mkdir(fqDirNme+'\\_access')
	if not os.path.isdir(fqDirNme+'\_access\pictura') :
		os.mkdir(fqDirNme+'\\_access\\pictura') 
	if not os.path.isdir(fqDirNme+'\_access\emblem') :
		os.mkdir(fqDirNme+'\\_access\\emblem') 
	

	fileSource = oldPaths.get(dirNme)

	
	marcDst = fqDirNme + "\\emblematica\\" + dirNme + "_marc.xml"
	marcFile = fileSource + "\\" + dirNme + "_marc.xml"
	if os.path.exists(marcFile) and os.path.isfile(marcFile) :
		shutil.copy2( marcFile, marcDst )
		
	marcFile = fileSource + "\\" + dirNme + "-MARC.xml"
	if os.path.exists(marcFile) and os.path.isfile(marcFile) :
		shutil.copy2( marcFile, marcDst )
	
	resp = requests.get(eachUrl)
	spine = resp.content

	parseXML(spine, dirNme, fqDirNme, fileSource)
	


	
	

	

		






