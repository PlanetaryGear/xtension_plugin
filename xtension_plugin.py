# -*- coding: utf-8 -*-
#
#		XTENSION PLUGIN STANDARD INCLUDE   http://MacHomeAutomation.com
#		Plugin Version 3.4.2
#		API Version 2
#
#	this code provides the glue that can connect any other python code to XTension
#	as well as providing various connivence functions and classes to expedite that
#	part of the XTension distribution and is Copyright 2018-2019 by james@sentman.com
#
#	it is free and open source and offered in the hope that it will be useful but without
#	claiming to be free of bugs or suitable for any particular purpose. Do not use 
#	this to control any devices which might cause a problem if they were operated,
#	or if they failed to operate properly. IOW use at your own risk.
#	
# version 1:
#	initial release
# version 2: 
#	added default return value for xtCommand.get
# version 3 2/13/2019:
# 	added initial support for python 3
#	python 3 execution path on this machine is: #!/usr/local/bin/python3
#	python 2 execution path was #!/usr/bin/python
# version 3.1 4/5/2019
#	added XTension.setXTensionData( key, value) shortcut
# version 3.2 5/27/2019
#	attempt to make the entire framework unicode capable for both
#	python 3 and 2.7
#	added traceback to get better errors that will show where the error actually occurred
#	lastly added a check to the XTension.send routine to make sure that we're not writing unicode
#	strings to bytesio but rather encode them as utf8 back to a regular string which it seems to accept
# version 3.3 11/26/2019
#	updated the xtension.addCommandHandler and removeCommandHandler to accept a list of commands
#	updated the addScriptHAndler and removeScriptHandler to also accept a list
#	added the addAllScriptHandler and removeAllScriptHandler functions
# version 3.3.1 3/1/2020
#	fixed typo in the parmParameterList vs paramParameterList in the shared script objects
#	executeHandler routine that would have caused an error rather than the script to execute it's handler
# version 3.3.2 4/27/2020
#	added check to xtData.clone to make sure that when cloning the uniqueid is always sent as a string regardless of its type carrier
# version 3.4 6/3/2020
#	added new unit direct command senders for:
#		XTUnit.sendNoOp( extradata, **kwds)
#		XTUnit.setDefaultLabel( newLabel) - this should not be used except when you dont want to include it in a commandm sends a noop with the new label
#	added ability for you to subscribe to a list of keys in an xData object that will be sent to you as a list
#	after the new values have been merged. This way you get one callback for all of them and not a separate one
#	for each before they are all applied
#		xtData.subscribeForList( [list, of keys], callback, tag)
#		xtData.unsubscribeForList( [list, of, keys], callback)
#	callback is in the form theCallback( theList, reference to the xtData object)
#	theList is a list of tuples such that [ (key, value, tag), (key, value, tag), ...]
# version 3.5 7/6/2020
#	added support for serial port in the XTRemoteConnection class. NO longer necessary to create a separate per plugin handler
#	for just normal serial port access. The XTRemoteConnection class will just automagically open either a remote TCP
# 	port or a serial port based on the selection of the user. If a serial port is allowed as an option then there should be
#	in the info.json the xtKeyBaud and other constants to properly setup the port or pass those same keys to the 
#	constructor kwargs of the XTRemoteConnection object. They will be ignored for TCP connections.
#	the XTRemoteConnection class getParm call will also now check in the XTension.info file for the key to exist
#	as a last resort before returning the default, if any.
#	Enforced script handler names being all lower case both at trying to find them and also at registering them
# version 3.5.1 11/9/2020
#	added the xtUnit.getProperties() command to more easily return a reference to the unit properties
#	NOTE this does not work yet as the back and forth needs some further infrastructure that is not complete
# version 3.4 12/7/2020
#	changes for the embedded python 3.7 version rather than whatever the system version happens to be
#	this will now be forever separate from the legacy version which is still included until ALL the plugins are updated
#	to use python 3.7 which will take some time if it is ever truly necessary. All new plugins from this moment forward
#	should be written to use python3.7 and contain that key in the info.json file. If so then this will be the version of the
#	plugin that is included.
# version 3.4.1 12/17/2020
#	added support for passing "debug" as the last parameter to startup the connection in debug mode
# version 3.4.2 4/10/2021
#	fixed error with new "getBlocked" method in XTUnit class which would always return blocked if the unit had ever been blocked


import sys
import socket
import traceback

try:
	import cStringIO
	isPy3 = False
	
except ImportError:
	from io import BytesIO
	isPy3 = True

#
#	TODO fix these imports that that it's not necessary to import some of them twice
#	now that I understand the naming and packaging conventions better than when I 
#	started this project.
from struct import *
import time
from time import *
from datetime import datetime
import threading
from threading import *
import io
import os
import json
import serial
import math
import uuid 

# try to set the process title to our plugin instance name if possible
# this still doesnt work for activity monitor or top, but ps will show the right thing
# actually this doesnt work at all yet so ignore it for the moment
# try:
# 	import setproctitle
# except:
# 	pass

try:
	from xtension_constants import *
except ImportError:
	from xtension_plugin.xtension_constants import *
	
	
	


xtensionPluginVersion = 4

# debugging aid during utf8 handling
# instead of sending writeLog commands through the proper channels
# this will redirect them just to stdout which also goes to the XTension log
# so that if the entire command system is broken you can still debug
logToPrint = False



class cXTension:

	#
	# all your global settings are in this xtData object by key
	# including any custom data that has been added via the json plugin file
	# containing all your custom controls. Target IP address and so forth for your
	# device or serial port name and such will be in here. See the XTConstants.py file
	# these will not be available until after the connection to XTension has succeeded
	# when the settings are received this will become an xtData object
	#
	settings = None
	
	#
	# set from XTension when extra logging is desired
	# you can check this within the XTension module or also register for the 
	# command xtCommandSetDebugMode and check the xtKeyValue property against xtTrue and xtFalse
	# to learn the new value
	#
	debugMode = False
	
	#
	# used internally to make sure the connection to XTension is up and running before doing things
	# like writing to the log during startup and such. If a write log command is issued before the connection
	# to XTension can receive it then the output will instead be printed to stdout
	# which will also show up in the XTension log or in the terminal if testing separately
	#
	ready = False
	
	#
	# Unit indexes maintained by the cXTension object
	# upon startup XTension will send you any units that are assigned to your interface
	# or all the units if you have requested access to the entire database
	# will be here. If you create new units in code or the user creates them later
	# the newUnit event will fire and you can be alerted to that. They will already have
	# been placed into the indexes at that point and be available for control
	#
	unitIndexByAddress 	= {}
	unitIndexById 		= {}
	unitIndexByName 	= {}
	
	#
	# shared script indexes if you're sharing the database then these can be used to look up
	# scripts that were shared with you.
	#
	
	scriptIndexById 	= {}
	scriptIndexByName 	= {}
	
	#
	# shared list indexes
	#
	listIndexById 		= {}
	listIndexByName 	= {}
	
	#
	# handlers that you may set to be called upon certain actions
	#
	
	# if you subclassed the xtUnit class then implement this
	# event. It will pass you the data object that defines the unit. You should
	# make a new instance of your subclass and pass the data object up to the Super __init__
	# so that other data structures can be setup properly. Then you can subclass any of the 
	# other handlers in the class.
	
	onMakeNewUnit 	= None
	
	# when a unit is received that is not yet in our indexes
	# this will be called with a single parameter of the xtUnit object
	onNewUnit 		= None 
	
	
	# called the first time that configuration data is received from XTension
	# this will only be called once. After that changes in settings should be tracked via
	# the subscribers function of the xtData class if you need immediate events for them
	onGotSettings 	= None	
	
	# called on startup when the first set of units is received from XTension
	# this is not called again even though new units may be created at any time
	# do initial config here only or you can do it in the onMakeNewUnit handler if you 
	# need specific data when a unit is created to set it up
	onGotUnits 		= None
	
	#
	# called when a new script is received that hasn't been seen before
	#
	onNewScript 	= None
	onMakeNewScript = None
	
	#
	#	list handling
	#
	onNewList 		= None

	
	#
	# registered callbacks by command type
	# the actual contents of the dictionary are an array so that the internal handlers
	# will always be called but that a user can add more via the addCommandHandler command
	# Do not access this directly
	_commandHandlers = {} 
	_scriptHandlers = {}
	_allScriptHandlers = [] # added in 3.3 so that you could trap all script handlers
	
	
	isShuttingDown = False
		
	
	def __init__(self):

		# it appears this is not necessary as b'' on python3 is just str as if it wasn't there	
		if isPy3:
			self._commandBuffer = b''
		else:
			self._commandBuffer = ''
	
		self.data = {} #all params stored in here
		self.writeLock = threading.Lock() #make sure 2 commands don't write in the middle of each other
		# keep a global reference in this module for us ot be able to do things like writeLog and such
		global XTension
		XTension = self
		
		# because I never remember the name of that call we will set it to both obvious things:
		
		self.getUnitWithAddress = self.getUnitFromAddress
		
		#
		#	load our info file as we may need serial information from it among other things
		#
		self.info = None
		self.loadInfoFile()
		
		# used for error messages and the shutdown message
		# is set when we receive our configuration from XTension
		self.interfaceName = '(not set)'
		self.interfaceId = None
		self.helloMessage = 'Python APIv3' # change before you call startup to change the hello message, just for logging of errors
		
		# for future checks to make sure the connection is valid
		self.ready = False
		self.gotSettings = False
		self.gotUnits = False
		
		# current run state so we dont sent constant updates to XTension
		self.currentRunState = ''
		
		# add our internal command handlers
		self.addCommandHandler( xtCommandSetMyUnits, self.event_receivedData)
		self.addCommandHandler( xtCommandShutdown, self.event_shutdown)
		self.addCommandHandler( xtCommandSetDebugMode, self.event_setDebug)
		self.addCommandHandler( xtCommandPing, self.event_respondToPing)
		self.addCommandHandler( xtCommandSetKeyedData, self.event_gotSettings)
		self.addCommandHandler( xtCommandScriptHandler, self.event_runScriptCommand)
		
		# waiting sync object going upstream to XTension to be merged back into the settings
		# and the thread that would send it
		
		self.settingsToMerge = None
		self.settingsMergeThread = None
		
		
		#	JFS 3.4.1 12/17/2020
		# attempt to get the final parameter passed and if it is "debug" then we are starting up in debug mode
		# this will just fail if there is no 4th parameter and debug mode will remain false
		try:
			if sys.argv[4] == "debug":
				self.debugMode = True
				print( "plugin starting in debug mode")
		except:
			pass
		



		
		
		

		# called separately and not during init so that you can insert an xUnit 
		# creation handler before the units are received from XTension
	def startup( self):
	


		
		# get our XTension address, port and ID from the command line
		self.XTensionAddress = sys.argv[1]
		self.XTensionPort = int( sys.argv[2])
		self.XTensionConnectionId = sys.argv[3]
		
		#print self.XTensionAddress, str( self.XTensionPort), str( self.XTensionConnectionId), "\r"
		

		# make the socket and connect, or try to
		self.sock = socket.socket( socket.AF_INET, socket.SOCK_STREAM)
		self.sock.connect((self.XTensionAddress, self.XTensionPort))
		
		# this is the first connect message the only important part is the connection ID
		# as that matches this socket up with the appropriate interface inside XTension
		# it's passed to us on the command line when we are started up
		self._rawWrite( self.helloMessage + ":" + self.XTensionConnectionId + "\r") #connect us to our interface instance inside XTension		

		self.ready = True
		
		# begin the listening on the port
		# which is done in this thread
		readThread = Thread( target=self.threadedRead, args=(), name='XTension Receive Thread')
		readThread.start()
		
		# ask for our settings and our units
		self.getMySettings() # ask for our all keyed data object
		self.getMyData() # ask for all the objects assigned to us
		
		# now wait for the settings and units to be received
		while not self.gotSettings or not self.gotUnits:
			sleep( 0.5)
			
	
	
	#
	#
	#	L O A D   I N F O   F I L E
	#
	#	loads the info.json file, if possible so that we will have access to the various 
	#	settings and information therein. This is loaded during the init call and does not wait
	# 	until the call to setup so that this will be available right away.
	#	alternatively this could be included in the data set from XTension but for the moment
	#	it is not.
	
	def loadInfoFile( self):
		try:
			with open( os.path.join( sys.path[0], "info.json"), "r") as info_file:
				try:
					self.info = json.load( info_file)
				except Exception as e:
					print( "XTension: error opening info.json file: %s" % e)
					self.info = None
		except Exception as e:
			print( "unable to open info.json file, this plugin is invalid")
			self.info = None
		

		#
		# DO SCRIPT COMMAND
		#
		# the handler you registered should take 2 parameters, the first will be an array of any
		# positional parameters used in the script call like doMyThing( one, two, three) 
		# the second is an xtData object that represents any other info if instead the command
		# was coming from a user using a dynamic interface element and such. Everything you need to
		# use that info is included with that element
		#

	def event_runScriptCommand( self, theCommand):
	
		
		commandName = theCommand.get( xtKeyAddress).lower()
		
		#XTension.writeLog( "in event_runScriptCommand commandName=" + commandName, xtLogRed)		

		positionalParms = None
		dataParms = xtData(theCommand) # will get the xtData object from the xtKeyData value in the command
		
		
		# positional parms will be named in the data object starting "_value" and a number in sequence
		# keep adding them to the array until you don't find one anymore
				
		positionalKey = "_value"
		workKey = positionalKey + "0"
		keyIndex = 0
					
			
		while dataParms.exists( workKey):
			if positionalParms == None:
				positionalParms = []
				
			workValue = dataParms.get( workKey)
			if type( workValue) == bytes:
				workValue = workValue.decode( 'utf-8')
				
			positionalParms.append( workValue)
				
			keyIndex += 1
			workKey = positionalKey + str( keyIndex)
		  
		
		
		# if the command is being sent to a unit instead of just to the interface itself 
		# then we can get it's tag and address here and pass the handler off to any 
		# unit subclass registerees for that name
		
		if dataParms != None:
			if dataParms.exists( xtKeyAddress) and dataParms.exists( xtKeyTag):
				#XTension.writeLog( "thereis a unit and tag")
				#this is being sent to a unit so we can pass this off to the unit
				workUnit = self.getUnitFromAddress( dataParms.get( xtKeyTag), dataParms.get( xtKeyAddress))
				if workUnit != None:						
					workUnit._runScriptCommand( commandName, positionalParms, dataParms)

		# 3.3 support for the AllScriptHandlers list as well
		for thisHandler in self._allScriptHandlers:
			try:
				thisHandler( commandName, positionalParms, dataParms)
			except Exception as e:
				XTension.writeLog( "Error in allScriptHandler( '" + commandName + "'): " + str( e), xtLogRed)
				XTension.writeLog( traceback.format_exc(), xtLogRed)

		
		if not commandName in self._scriptHandlers:
			# no handler was found, log if in debug mode 
			XTension.debugLog( "no global handlers for script command (" + commandName + ")")

			return
		
		for workHandler in self._scriptHandlers[ commandName]:
			try:
				workHandler( commandName, positionalParms, dataParms)
			except Exception as e:
				XTension.writeLog( "Error handling command '" + commandName + "' " + str( e), xtLogRed)
				XTension.writeLog( traceback.format_exc(), xtLogRed)

			
		



		
	#
	#
	#	S H U T D O W N
	#
	#

	def event_shutdown( self, theCommand):
		self.writeLog( "shutting down...")
		# setting this will cause the main loops in all our threads to drop out within a second
		# so that we can cleanly quit
		self.isShuttingDown = True
		sleep( 1) #just make sure our log message has made it to XTension before we quit.

	
	
	#
	#
	#	D E B U G
	#
	#
		
	def event_setDebug( self, theCommand):
			
		if theCommand.get( xtKeyValue) == xtTrue:
			self.debugMode = True
			self.writeLog( "debug mode is enabled", 4)
		else:
			self.writeLog( "debug mode is disabled", 4)
			self.debugMode = False




	#
	#
	#	P I N G
	#
	#
			
	def event_respondToPing( self, theCommand):		
		self.sendCommand( XTCommand( xtKeyCommand = xtCommandPingResponse))			
	
	
	
	#
	#
	#	G E T   U N I T   F R O M   A D D R E S S
	#
	# pass the unit tag and address to get the xtUnit object out of the index
	#
	# you can also use the keyed entries of tag= and address= to pass through
	# in order to avoid confusion about which parameter comes first
	def getUnitFromAddress( self, tag = None, address = None, **kwargs):
		# addresses in XTension are always uppercase so make sure
		# that is set here or it won't find your unit
		
		if tag == None and 'tag' in kwargs:
			tag = kwargs[ 'tag']
		
		if address == None and 'address' in kwargs:
			address = kwargs[ 'address']

		addressPath = ""
		if tag:
			addressPath += str( tag);
		
		if address:
			try:
				addressPath += address.upper()
			except:
				addressPath += str( address).upper()
			
		
		if addressPath in self.unitIndexByAddress:
			return self.unitIndexByAddress[ addressPath]
		else:
			self.debugLog( "---UNIT NOT FOUND AT PATH: (%s)" % addressPath)
			return None
	
	#
	#	G E T   U N I T   W I T H   A D D R E S S
	#
	# the init function sets self.getUnitWithAddress to be the same as the above
	# getUnitfromAddress as the syntax is awkward in both cases and I never remembered which
	# was correct, so now both are correct. Though I think that getUnitWithAddress makes more sense
	#


	
	
	#
	#	D E B U G   D U M P   U N I T S
	#
	#	just a debugging aide to output all the units that are in the index
	#	in case things are 
	def debugDumpUnits( self):

		XTension.writeLog( "BEGIN DEBUG DUMP UNITS", xtLogGreen)
		XTension.writeLog( "len( self.unitIndexByAddress) = %s" % len( self.unitIndexByAddress), xtLogGreen)

		for workPath in self.unitIndexByAddress:
			thisUnit = self.unitIndexByAddress[ workPath]
			XTension.writeLog( "UNIT: %s PATH: %s ADDRESS: %s TAG: %s ID: %s" % (thisUnit.name, workPath, thisUnit.address, thisUnit.tag, thisUnit.uniqueId))
		
		XTension.writeLog( "END DEBUG DUMP UNITS", xtLogGreen)

	
	
	#
	#
	#	G E T   U N I T   I G N O R I N G   T A G
	#
	#	sometimes useful to be able to get a unit reference without knowing the tag
	#	ahead of time. Useful for incoming commands from a device where the address will
	#	be unique and the tag would not be known until the unit subclass is returned
	#	this is not as efficient a routine however as I don't yet maintain a separate index
	#	by this so the array must be walked to find it. This will not work if the
	#	address might be duplicated across tag types
	#
	def getUnitIgnoringTag( self, address):
		address = address.upper()
		for key in self.unitIndexById:
			workUnit = self.unitIndexById[ key]
			if workUnit.address == address:
				return workUnit
		
		return None
		
	#
	#	G E T   U N I T   I G N O R I N G   A D D R E S S
	#
	#	sometimes you may only ever have one unit with a particular tag and you 
	#	may not know the address the user has given it or it just doesn't matter because
	#	there can be only one. This will return the first unit it finds with the passed
	#	tag. It will ignore multiples.
	def getUnitIgnoringAddress( self, tag):
		for key in self.unitIndexById:
			workUnit = self.unitIndexById[ key]
			if workUnit.tag == tag:
				return workUnit
		
		return None
	
	
	#
	#	G E T   U N I T   F R O M   I D
	#
	# shortcut for getting a unit via it's unique id
	# useful for sharing plugins where this is the normal way of 
	# getting a unit reference
	#
	def getUnitFromId( self, id):
		# id's are always stored as a string
		# because converting to a float screws up the 
		# string index value. So make sure this is a string
		
		if not isPy3:
			id = id.encode( 'utf-8')

		if id in self.unitIndexById:
			return self.unitIndexById[ id]
		else:
			return None
			
	#
	#	G E T   S C R I P T   F R O M   I D
	#
	def getScriptFromId( self, id):
		
		
		if not isPy3:
			id = id.encode( 'utf-8')
			

		if id in self.scriptIndexById:
			return self.scriptIndexById[ id]
		else:
			return None
		
	#
	#	G E T   L I S T   F R O M   I D
	#
	def getListFromId( self, id):
	
		if id in self.listIndexById:
			return self.listIndexById[ id]
		else:
			return None
			
				
	#
	#
	#	T H R E A D E D   R E A D
	#
	#
	# internal, this is what reads the data from the socket from XTension and handles it
	#
	def threadedRead( self):
		# called from the init method once the socket has been closed and we are now threaded
	
		while True:
		
			newData = self.sock.recv( 4028)
			if newData == b'':
				if self.isShuttingDown:
					print( "XTension pipe has been closed")
					break
				else:
					print( "there was an error on the pipe to XTension\r")
					self.ready = False
					sys.exit()
					# an then XTension will try to restart us
				
			
			self._commandBuffer += newData
			
			

			while len( self._commandBuffer) > 4:
		
				
				packetHeader = self._commandBuffer[:1]
					
				if packetHeader == b"J":
					packetSize = unpack( "H", self._commandBuffer[1:3])[0]
				elif packetHeader == b"K":
					packetSize = unpack( "I", self._commandBuffer[1:5])[0]
				else:
					# an unknown packet header has been received
					# assuming garbage in the buffer or a malformed packet or something
					# we need to shrink the buffer until we find the next potentially
					# valid header and start trying to read from there. That might not work
					# of course and we should probably quit and let XTension restart us
					# but we will try
					self._commandBuffer = self._commandBuffer[:1]
					continue
				

			
				# if we do not have enough data to parse the packet yet then just return and wait
				# for the next read.
				if len( self._commandBuffer) < packetSize:
					break
			
				# pop the packet off the front of the buffer 
				thisPacket = self._commandBuffer[0:packetSize]
				self._commandBuffer = self._commandBuffer[packetSize:]
				
				workCommand = XTCommand()
				workCommand._parse( thisPacket)
								
				
				if not workCommand.isValid:
					self.writeLog( "Command from XTension failed to parse", xtLogRed)
					#dont try to actually do anything with a failed packet
					continue
				
					
				#if self.debugMode and workCommand.get( xtKeyCommand) != xtCommandPing:
				#	self.writeLog( "command from XTension (%s)" % workCommand.get( xtKeyCommand))
				#	workCommand._debugLog()

				

				#XTension.writeLog( 'tag=(%s) address=(%s)' % (workCommand.get( xtKeyTag, '(none)'), workCommand.get( xtKeyAddress, '(none)')))
				#workCommand._debugLog()

				# if the packet has both an address and an address prefix then this command
				# is destined for a specific unit. Find the unit in our index and send it on
				if xtKeyTag in workCommand.values and xtKeyAddress in workCommand.values:
					workUnit = self.getUnitFromAddress( workCommand.get( xtKeyTag), workCommand.get(xtKeyAddress))
					
					if workUnit != None:
						
						try:
							workUnit.handleCommandFromXTension( workCommand)
						except Exception as e:
							XTension.writeLog( "error handing (" + workCommand.get( xtKeyCommand) + ") from XTension: " + str( e), xtLogred)
							XTension.writeLog( traceback.format_exc(), xtLogRed)
							
				# the other way of addressing an object is via the unique id and a target value that tells us what object to send it to
				# if this command has both a command target and a unique ID then it is this type of command and we can route it per that.
				elif xtKeyCommandTarget in workCommand.values and xtKeyUniqueId in workCommand.values:
					
					#
					# what is the target of the delete message
					# this was previously used just for units as it's the deleteunit command
					# however it's now used for all shared objects as well. When it's deleted
					# or when it's no longer shared to us then we will be sent this message
					# that we should handle and treat that unit or object as no longer ours
					# to control or monitor
					#
					thisTarget = workCommand.get( xtKeyCommandTarget)
					
					#
					# target unit
					#
					if thisTarget == xtTargetUnit:
						workUnit = self.getUnitFromId( workCommand.get( xtKeyUniqueId))
						if workUnit != None:
							try:
								workUnit.handleCommandFromXTension( workCommand)
							except Exception as e:
								XTension.writeLog( "error handling (" + workCommand.get( xtKeyCommand) + ") to Unit: " + str( e), xtLogRed)
								XTension.writeLog( traceback.format_exc(), xtLogRed)

						else:
							self.writeLog( "Unable to handle command for unit:", xtLogRed)
							workCommand._debugLog()
					
					#
					# target script
					#
					
					elif thisTarget == xtTargetGlobalScript:
						workScript = self.getScriptFromId( workCommand.get( xtKeyUniqueId))
						if workScript != None:
							try:
								workScript.handleCommandFromXTension( workCommand)
							except Exception as e:
								XTension.writeLog( "error handling (" + workCommand.get( xtKeyCommand) + ") to Script: " + str( e), xtLogRed)
								XTension.writeLog( traceback.format_exc(), xtLogRed)

						else:
							self.writeLog( "Unable to handle command for script:", xtLogRed)
							workCommand._debugLog()
							
					
					#
					# as more objects are supported they should be handled here
					# TODO lists are already supported but not in the plugin code
					#
					

				# now look for any other handlers that are registered for this command type and forward that through as well								
				# pull out the command code to see if we have a higher level handler for the command to call
				thisCommandCode = workCommand.get( xtKeyCommand, "(none)")
				
				if thisCommandCode in self._commandHandlers:
					for workHandler in self._commandHandlers[ thisCommandCode]:
						try:
							workHandler( workCommand)
						except Exception as e:
							XTension.writeLog( "error handling (" + workCommand.get( xtKeyCommand, "no command") + ") from XTension: " + str( e), xtLogRed)
							XTension.writeLog( traceback.format_exc(), xtLogRed)
						
				#special handling for shutdown command, have to exit here so that multiple other commands
				# can be executed to shutdown other sockets or anything else
				# if you call sys.exit in any of the other added handlers then this will fall out and the remainder of them
				# will never be called. So i will take care of that here you don't have to do that in your shutdown handlers.
				
				if thisCommandCode == xtCommandShutdown:					
					try:
						self.sock.shutdown(socket.SHUT_RDWR)
						self.sock.close()
					except:
						pass
						
					self.ready = False
					sys.exit()
						
				# ack that we received the command
				ackCommand = XTCommand()
				ackCommand.set( xtKeyCommand, xtCommandAck)
				ackCommand.set( xtKeyPacketId, workCommand.get( xtKeyPacketId))
				self.sendCommand( ackCommand)

	
	#
	#	D O   S H U T D O W N
	#
	#	called by the script when we want to be restarted by XTension, this basically
	# 	just mimics the reception of the shutdown command and all events should trigger based
	# 	on that and the script will quit, but XTension did not shut it down so it will restart
	#	it in 5 seconds with the new settings or for whatever other reason.
	# 	this handler does no logging, you should log the reason why this is happening or
	#	necessary before you call this.
	#
	def doShutdown( self):

		# make a command to pass to the handlers so there is no error
		shutdownCommand = XTCommand( xtKeyCommand = xtCommandShutdown)
		
		if xtCommandShutdown in self._commandHandlers:
			for workHandler in self._commandHandlers[ xtCommandShutdown]:
				try:
					workHandler( shutdownCommand)
				except Exception as e:
					XTension.writeLog( "error in doShutdown handler: " + str( e), xtLogRed)
					XTension.writeLog( traceback.format_exc(), xtLogRed)

		# now that we are not closing the socket in the handler we registered we should also do it here
		# paainf RDRW should send the meta data upstream that we are closing both the read and write paths
		# and so the upstream device should send the appropriate error code that we have been disconnected.
		# otherwise it can wait the entirety of the TCP timeout value which can be forever, or 2 minutes
		# whichever comes first.
		try:
			self.sock.shutdown( socket.SHUT_RDWR)
			self.sock.close()
		except:
			pass
			
		self.ready = False

		sys.exit()

								
				
				
	#
	#
	# 	R E C E I V E D   U N I T S 
	#
	#
	#	called when we receive our initial dump of units from XTension 
	# 	called when XTension sends us either an update to a unit or a new unit
	# 	manages the loading of the new xtUnit object and placing it into the index
	# 	will then call the Received New Units callback if any has been specified
	#
	def event_receivedData( self, theCommand):
	
	
		myData = xtData(theCommand)	
		newUnits = myData.getAllContainers( "unit")
				
		for x in newUnits:

			workId = x.get( xtUnitKeyUniqueId, None)
	
			if workId == None:
				XTension.writeLog( "no unique id found in unit data", xtLogRed)
				x._debugLog()
				continue
				
			# if the unit already exists then merge it's data with the new data
			# do not re-create the unit
			if workId in self.unitIndexById:
				workUnit = self.unitIndexById[ workId]
				workUnit.mergeFromData( x)
			
			# if the unit does not exist then create it
			else:
				if self.onMakeNewUnit == None:
					workUnit = XTUnit( x)
				else:
					workUnit = self.onMakeNewUnit( x)
					# if they didn't return anything then we should create it
					if workUnit == None:
						workUnit = XTUnit( x)
		
		#
		# if this is the first time we're being loaded then run the onGotUnits handler if any
		#
# 		if not self.gotUnits:
# 			self.gotUnits = True
# 			
# 			if self.onGotUnits != None:
# 				self.onGotUnits()
				
		#
		# and now look for any scripts being shared with us
		#
		
		newScripts = myData.getAllContainers( "script")
		
		for x in newScripts:
			workId = x.get( xtUnitKeyUniqueId, None)
			
			if workId == None:
				XTension.writeLog( "no unique id found in script data", xtLogRed)
				x._debugLog()
				continue
			
			# if the script already exists then merge its data with the new data
			if workId in self.scriptIndexById:
				workScript = self.scriptIndexById[ workId]
				workScript.mergeFromData( x)
			
			# if the script does not exist then create it
			else:
				if self.onMakeNewScript == None:
					workScript = xtScript( x)
				else:
					workScript = self.onMakeNewScript( x)
					
				# if a gotNewScript handler has been installed then call it
				if self.onNewScript != None:
					self.onNewScript( workScript)


		#
		#	load lists
		#

		newLists = myData.getAllContainers( "list")
		
		for x in newLists:
			workId = x.get( xtUnitKeyUniqueId, None)
		
			if workId in self.listIndexById:
				workList = self.listIndexById[ workId]
				workList.mergeFromData( x)
			else:
				workList = XTList( x)
			
			if self.onNewList:
				self.onNewList( workList)
			
			
				
			
				
				
			
		#
		# if this is the first time we're being loaded then run the onGotUnits handler if any
		#
		if not self.gotUnits:
			self.gotUnits = True
			
			if self.onGotUnits != None:
				self.onGotUnits()
						
	
	#
	# A D D   C O M M A N D   H A N D L E R
	#
	# if you want to handle a specific incoming command from XTension you can call this
	# method to add yourself to the list of callbacks to make when that command is received
	# the parameters passed to the callback will be the single parameter of theCommand
	# containing the xtCommand object that was received.
	#
	#
	
	def addCommandHandler( self, commandCodeList, theCallback):
	
		# if it's not a list then turn it into a list
		if not isinstance( commandCodeList, list):
			commandCodeList = [commandCodeList]
		
		for commandCode in commandCodeList:
			if not commandCode in self._commandHandlers:
				self._commandHandlers[ commandCode] = [theCallback]
			else:
				self._commandHandlers[ commandCode].append( theCallback)
	
	
	#
	#	R E M O V E   C O M M A N D   H A N D L E R
	#
	def removeCommandHandler( self, commandCodeList, theCallback):
		
		if not isinstance( commandCodeList, list):
			commandCodeList = [commandCodeList]
			
		for commandCode in commandCodeList:
	
			if commandCode in self._commandHandlers:
				self._commandHandlers[ commandCode].remove( theCallback)

				# if there are no more command handlers in the list for this command code
				# then delete it entirely from the dictionary of command handlers
				if len( self._commandHandlers[ commandCode]) == 0:
					del( self._commandHandlers[ commandCode])
			
		
	#
	# A D D   S C R I P T   H A N D L E R
	#
	#
	
	def addScriptHandler( self, theNameList, theCallback):
	
		if not isinstance( theNameList, list):
			theNameList = [theNameList]
			
		for theName in theNameList:
			# enforce them being all lowercase v3.5
			theName = theName.lower()
	
			if not theName in self._scriptHandlers:
				self._scriptHandlers[ theName] = [theCallback]
			else:
				self._scriptHandlers[ theName].append( theCallback)
			
	#
	# R E M O V E   S C R I P T   H A N D L E R
	#
	def removeScriptHandler( self, theNameList, theCallback):
	
		if not isinstance( theNameList, list):
			theNameList = [theNameList]
			
		for theName in theNameList:
			# enforce them being all lower case v3.5
			theName = theName.lower()
			
		
			if theName in self._scriptHandlers:
				# this is a syntax error
				# you can't remove something from a list object like this
				#self._scriptHandlers[ theName].remove[ theCallback]
				self._scriptHandlers[ theName].remove( theCallback)
				
				# if we removed them all then we don't need an empty list stored in the dict either
				if len( self._scriptHandlers[ theName]) == 0:
					del( self._scriptHandlers[ theName])
			
			
	#
	#	A D D   A L L   S C R I P T   H A N D L E R
	#
	#	added in 3.3 so that you can trap every script command if you wished
	#
	def addAllScriptHandler( self, theCallback):
		if theCallback in self._allScriptHandlers:
			return
			
		self._allScriptHandlers.append( theCallback)
		
	#
	#	R E M O V E   A L L   S C R I P T   H A N D L E R
	#
	#	added in 3.3 see addAllScriptHandler above
	#
	def removeAllScriptHandler( self, theCallback):
		if not theCallback in self._allScriptHandlers:
			return
		
		self._allScriptHandlers.remove( theCallback)
		
		
		
		

		

	#
	#
	#	S E N D   C O M M A N D
	#
	#
	# sends a command to XTension
	#
	def sendCommand( self, theCommand):

		# debug sends but do NOT do so if its a log command or we get stuck in a loop
		# until we crash...
		#if self.debugMode and theCommand.get( xtKeyCommand) != xtCommandWriteLog:
		#	theCommand._debugLog()
		
		try:
			self.writeLock.acquire()
			theCommand.send()
			self.writeLock.release()
		except:
			self.writeLock.release()
			XTension.writeLog( traceback.format_exc(), xtLogRed)
		
		
	
	
	#
	# Internal function to directly write to the Socket
	# Do not call this directly. This does not lock the 
	# semaphore for writing either
	#
	def _rawWrite( self, msg):
	
		try:
			if isPy3:
				if type( msg) != bytes:
					msg = msg.encode()
				
				self.sock.sendall( msg)
			else:
				totalsent = 0
				while totalsent < len( msg):
					sent = self.sock.send( msg[totalsent:])
				
					if sent == 0:
						raise RuntimeError( "socket connection broken")
					totalsent = totalsent + sent
		except:
			pass # this just means the connection to XTension has been closed so ignore it
	
	
	
	#
	#
	#	S E T   R U N   S T A T E
	#
	#
	#	changes the run state in XTension
	# 	pass xtRunStateOK, xtRunStateErr or xtRunStateFail
	# 	and any descriptive message as to why
	#
	
	def setRunState( self, newState, message):
		if not self.ready:
			print( "device run state set to " + newState + " before a valid connection to XTension was established.\r")
		else:
			if newState != self.currentRunState:
				self.currentRunState = newState
				
				self.sendCommand( XTCommand(
					xtKeyCommand 			= xtCommandSetRunState,
					xtKeyValue				= newState,
					xtKeyErrorMessage		= message))	
	
	#
	#
	#	W R I T E   L O G
	#
	#
	# writes to the XTension log
	# color can be 1 = black, 2 = blue, 3 = green, 4 = red or a 6 character hex string
	#
	# see also the write log method in the xtUnit class. If logging for unit specific info
	# or errors you should use that method as it allows the log line to be filtered by the
	# master log window in XTension
	#
	def writeLog( self, msg, color="2"):
	
		if not isPy3:			
			#msg = msg.encode( 'utf-8')
			# the above doesn't actually work if the msg is an str with unicode chars in it
			# in that case we have to cast as below, but only if it's not already unicode as
			# casting to unicode from unicode which should just do nothing actually throws
			# an error. Stupid Stupid Unicode!
			
			# there is something that passes an msg of None here? that is VERY strange but we need to 
			# handle that without breaking the read thread
			
			try:
				if msg == None:
					return
			
				if type( msg) != unicode:
					msg = unicode( msg, 'utf-8')
			except Exception as e:
				print( "error in write log %s (%s)" % (e, msg))
				return

		# logToPrint is set at the top as a debugging aid so that you can write to the log
		# even if the entire messaging structure is broken. I needed that when doing the
		# unicode support
		# removed check for isShuttingDown as we actually want to be able to log in that case still
		
		#if not self.ready or self.isShuttingDown or logToPrint:
		if not self.ready or logToPrint:
			try:
				print( msg )
			except Exception as e:
				print( "--------> unable to print log (" + str( e) + ")")
				print( "type=%s" % str( type( msg)))
				print( "(%s)" % msg.encode( 'utf-8'))
				print( traceback.format_exc(), xtLogRed)
				
		else:
			self.sendCommand( XTCommand(
				xtKeyCommand	= xtCommandWriteLog,
				xtKeyValue		= str( color),
				xtKeyData		= msg))

	#
	#
	# 	D E B U G   L O G 
	#
	#
	# can call this to do logging only when in debug mode
	# just a shortcut so that you don't have to check XTenison.debug every single time
	#
	
	def debugLog( self, msg, color="2"):

		if self.debugMode:
			# if we are not connected then we just print
			# as that will also end up in the XTension log but does not require
			# a valid connection.
			if not self.ready:
				print( msg)
			else:
				self.writeLog( msg, color)
			
	#
	#
	#	S E T   X T E N S I O N   D A T A
	#
	# Helper method to do a setXMLData command in XTension
	# this saves or changes information in your XTension.settings object
	# to set data in a unit there is a similar command in the xtUnit object
	# to make the changes live immediately we also set the value into the 
	# local object so that you don't have to wait till the change comes back from XTension
	#
	
	def setXTensionData( self, key, value):
		# set it in the local object so that it will be immediately available to this plugin
		# otherwise you'd have to wait for XTension to send the merged data back
		XTension.settings.set( key, value)
		
		
		self.sendCommand( XTCommand(
			xtKeyCommand	= xtCommandSetXMLData,
			xtKeyName		= key,
			xtKeyValue		= value))
						


	#
	#
	#	G E T   M Y   D A T A
	#
	# ask XTension to send us a dictionary for each of our units
	#
	def getMyData( self):
	
		self.sendCommand( XTCommand( xtKeyCommand=xtCommandGetMyUnits))	
	
	
	
	
	#
	#
	#	G E T   M Y   S E T T I N G S
	#
	# gets my settings and all configuration info
	# called during initial connection, after that they are kept up to 
	# date via the merge mechanism.
	#
	def getMySettings( self):
		self.sendCommand( XTCommand(
			xtKeyCommand 	= xtCommandGetKeyedData,
			xtKeyAddress	= 'all'))
		
		
		
	#
	#
	#	G O T   S E T T I N G S
	#
	# called when we receive our config that we requested above
	# at this point we have most information that we would need to
	# open up our connections and such so we call the onGotSettings
	# call back if it's set.
	#
	# note that the XTension units, if any, may not have been received yet so you should
	# be prepared to receive those later and link up anything necessary
	#
	def event_gotSettings( self, theCommand):
		if not theCommand.get( xtKeyAddress) == "all":
			#print( "got a keyed data object named: " + theCommand.get( xtKeyAddress) + "\r")
			# TODO make this able to send a keyed data object of other names as requested
			# right now you can only use the "all" object
			return
			
		workData = xtData( theCommand)
			
		if self.settings == None:
			self.settings = workData
			
			self.settings.subscribeToChildren( self.settingChildCallback)
			
			# first time calling this execute the onGotSettings event if one was set
			
			if self.onGotSettings != None:
				self.onGotSettings()

			
		else:
			self.settings.merge( workData)

		self.interfaceName = self.settings.get( xtKeyName)
		self.interfaceId = self.settings.get( xtUnitKeyUniqueId) # in this case a simple string is returned with the value which is better
		
		self.gotSettings = True
		
	
	
	#
	#	settings child callback
	#
	#	if we change a setting locally in the plugin we will get this callback and
	#	we should create a command after a short delay to send the changes upstream to 
	#	XTension. This way we can keep the settings in sync and be changeable either in XTension
	#	or in the plugin. 
	def settingChildCallback( self, *a):
		# there is no waiting object yet to be sent, so just set it to the passed object
		if self.settingsToMerge == None:
			self.settingsToMerge = a[0]
			
			# and then startup the waiting timer thread that will send it in a tenth of a second
			# in case more changes show up within that time they can all go together rather than
			# causing a lot of extra message parsing.
			self.settingsMergeThread = Thread( target=self.settingsSyncCallback, args=())
			self.settingsMergeThread.start()
			
		else:
			# already a thread waiting for a tenth of a second for more data to come in so just
			# merge the two things.
			self.settingsToMerge.merge( a[0])
			

	def settingsSyncCallback( self):
		sleep( 0.1)
		x = self.settingsToMerge
		self.settingsToMerge = None
		
		
		
		XTension.sendCommand( XTCommand(
			xtKeyCommand 		= xtCommandSyncSettings,
			xtKeyData 			= x))
		
	
	
	
	#
	#
	#	E N C O D E   C O M M A   S E P A R A T E D
	#
	# just a helper function to encode a list to proper comma separated values for sending to the
	# execute script handler command.
	
	def encodeCommaSeparated(self, theList):

		p = []

		for s in theList:

			work = str( s)
			
			if '"' in work:
				work = work.replace( '"', '""')

			if "," in work or '"' in work:
				work = '"' + work + '"'
			
			p.append( work)
			
		return ",".join( p)
		
		
		
		
		
	#
	#	S E T   S T A T U S
	#
	# a helper function to write to the status line in the interface window in XTension
	# This will only send the command if the status has changed so you can call this without
	# checking for that
	#
	def setStatus( self, theStatus):
		
		if theStatus == self.settings.get( xtKeyDefaultInfoDisplay, ''):
			# same status line is being passed just ignore it
			return
		
		#
		# the local status will rapidly be updated to reflect this change
		# no need to force it locally, we will receive that merge command with the
		# new data from XTension momentarily.
		#
		
		self.sendCommand( XTCommand(
			xtKeyCommand 	= xtCommandSetXMLData,
			xtKeyName		= xtCommandSetStatus,
			xtKeyValue		= theStatus))
		
	#
	#	E X E C U T E   E R R O R   H A N D L E R
	#
	

		   
		
		
		
		
		
		
		
		

#
#
#	X T C O M M A N D
#
#
# the class for all commands to and from XTension
#
# changed the constructor to take **kwds) so that we can setup all the commands from a single
# instantiation is desired and moved the parsing to a separate command.
		
		
class XTCommand:
	
	def __init__(self, **kwds):
		self.values = {}
		self.isValid = False # will be set to true when we are parsed, ignored for outgoing commands
		
		# add in any values sent through the kwds object
		# optimization just ask for the gobals once and not every time through the loop
		
		currentGlobals = globals()

		for key in kwds:
			workValue = kwds[ key]
			# the constants for command are used for the kwrgs and so they will come through
			# as the constant name, so we need to convert them back to the actual value and not the
			# constant name.
			
			if key in currentGlobals:
				key = currentGlobals[key]
			#else:
				#if anything is passed which is not in the globals then we either hard coded the string we want to use
				# which is fine, or it is an error that will cause problems later so if in debug mode we should
				# output that this happened though it may not actually be an error
				#XTension.debugLog( "non-global key (%s) passed to XTComman Constructor" % key, xtLogRed)
				# actually it seems that there are a lot of these being used, but we can at least verify that they are 4 chars?
			
			self.set( key, workValue)
		

	#
	#
	#	S E T
	#
	# add keyed data to the command
	# note that all keys must be 4 characters or they will be truncated
	# all values are converted to strings before sending
	#
		
	def set( self, key, value):

		# if key is too short then add spaces to pad to 4 chars
		# this should not happen but it will break the command if it does
		# this will also fix things if the key is longer than 4 chars which would
		# also break things.
		
		if isPy3:
				
			# make sure is 4 chars 
			if len( key) < 4:
				key = (key + "    ")[:4]
				
			# look for a tuple and if that then encode it comma separated
			
			if type( value) == tuple or type( value) == list:
				value = XTension.encodeCommaSeparated( value)
				
			if type( value) == bool:
				if value:
					value = xtTrue
				else:
					value = xtFalse
			
			# allow for passing in xtData objects
			if type( value) == xtData:
				value = value.save()


			# values are always bytes in a command in python3
			if type( value) != bytes:
				value = str( value).encode()

			# but the byte like object into our dictionary
			self.values[ key[:4]] = value
			
		else:	# python 2.7
			if len( key) < 4:
				key = str( key + "    ")[:4]
				
			# look for a tuple and comma encode it
			
			if type( value) == tuple or type( value) == list:
				value = XTension.encodeCommaSeparated( value)
				
			if type( value) == bool:
				if value:
					value = xtTrue
				else:
					value = xtFalse
				
			if type( value) != unicode and type( value) != str:
				value = str( value)
			

			# don't want to force unicode here as the str() may have binary data in it from saving of an xData object
			self.values[ key[:4]] = value #unicode( value) # force the value to be a string

			
		
		
	#
	#
	#	G E T
	#
	# get keyed value out of the command
	# if the key does not exist then return the optional defaultValue or None
	# in python3 this will always return the value as a string
	# if you need the raw bytes as for loading an xtData object then
	# use the getBytes call
	#
	def get( self, key, defaultValue=None):
	
		# since the keys are always strings
		# but the values are always bytes make sure that the
		# keys are strings or they wont match
		if isPy3 and type( key) == bytes:
			key = key.decode()
			
		if not key in self.values:
			return defaultValue
		else:
		
			if isPy3:
				# values in self.values are always bytes in python3
				# so decode to string. If you need bytes data use getBytes
				return self.values[ key].decode()
			else:
				# all values are utf-8 encoded in python 2.7
				# if you need a raw str use the getBytes method
				work = self.values[ key]
				if type( work) != unicode:
					#work = work.encode( 'utf-8')
					try:
						work = unicode( work, 'utf-8')
					except Exception as e:
						XTension.writeLog( "%s: invalid characters in UTF-8 encoded string with key of: %s" % (XTension.interfaceName, key), xtLogRed)
					
				return work
			
	#
	#	G E T   B Y T E S
	#
	# used most commonly when you need the value as a bytes object for parsing out
	# an embedded xtData object
	#
			
	def getBytes( self, key, defaultValue=None):
	
		# why would the key ever be a bytes like object?
		if isPy3 and type( key) == bytes:
			key = key.decode()
			
	
		if  not key in self.values:
			return defaultValue
		else:
			return self.values[key]
		
		
		
	#
	#
	#	E X I S T S
	#
	# check to see if a key exists in the command
	#
	def exists( self, key):
		if isPy3 and type( key) == bytes:
			key = key.decode()
			
		return( key in self.values)
	
	
	
	
	#
	#
	#	D E B U G   L O G
	#
	# call this to see all the key=value pairs in the command
	#
	# also expose just as debugLog as it is too useful to think it is a private function
	#
	
	def debugLog( self):
		self._debugLog()
	
	def _debugLog( self):			
		try:
			for key, val in self.values.items():
				if key != xtKeyData:
				
					#py3 try to decode the value for printing
					if isPy3:
						if type( val) == bytes:
							val = val.decode()
						
					else:
						if type( val) != unicode:
							try:
								#val = val.encode( 'utf-8')
								val = unicode( val, 'utf-8')
							except:
								pass
				
					XTension.writeLog( key + "=" + val)
					#XTension.writeLog( "%s(%s)=%s(%s)" % (key, str( type( key)), val, str( type(val))))
				else:
					XTension.writeLog( key + "+raw data skipped")
		except Exception as e:
			XTension.writeLog( "unable to debug log (" + str( e) + ")")
	
	
	#
	#
	#	S E N D
	#
	# called by the XTension.send( theCommand) routine, do not call yourself
	# writes the raw data of the flattened command to the XTension pipe
	#
	def send( self):
	
		
		try:
	
			if isPy3:
				output = BytesIO()
			else:
				output = cStringIO.StringIO()
		
			# first char is a "K"
			# next 4 bytes are the length as uint32
			# then a flag byte which is 0 or &b1000000 to signify the little endianess of the data
		
			for key, val in self.values.items():
				
				if isPy3:
					# the key types are always going to be strings in by3 so
					# they must be encoded to byte like objects
					if type( key) != bytes:
						key = key.encode()
					
					# the val should already be a bytes like object as it's converted
					# in the set method, but idiot check to be sure
					if type( val) != bytes:
						val = val.encode()
						
				# in python 2.7 the type of val will always be either str or unicode
				# cannot convert at this point as it may include binary data
				
				# write the 4 byte key. 4 byte length is enforced by the set methods
				output.write( key)
				
				
				# write the length of the value as a 4 byte unsigned integer
				# but if we're a UTF-8 string then we need the byte length and not the
				# utf-8 length!
				if not isPy3:
					if type( val) == unicode:
						lenb = pack( 'I', len( val.encode( 'utf-8')))
					else:
						lenb = pack( 'I', len( val))
				else:
					lenb = pack( 'I', len( val))
					
				#lenb = pack( "I", len( val))
				output.write( lenb)
				
				#
				# there remains a problem with unicode here. We need to make sure that the
				# string is a type str and not type unicode, if it is unicode then we need to
				# "encode" it with encoding utf-8 in order to get it to go through
				#
				
				if not isPy3:
					if type( val) == unicode:
						val = val.encode( 'utf-8')
				
				# lastly write the value
				output.write( val)
			
			# get the raw either bytes value in py3 or str in py2 so that we can
			# pass it to the rawwrite method below
			
			rawCommand = output.getvalue()
			
			
			output.close()

			
			XTension._rawWrite( b"K")
			totalLen = pack( "IB", len( rawCommand) + 6, 128)
			XTension._rawWrite( totalLen)

			XTension._rawWrite( rawCommand)

			
		except Exception as e:
			# have to print here as if we are having command errors then we may be not be able to process
			# another one to send the log message. Though this does mean that the errors may be out of order
			# as processing from the 2 different queues will make things come in at different times.
			print( "exception in XTCommand.send: %s" % str( e))
			print( traceback.format_exc(), xtLogRed)
		
	#
	#
	#	P A R S E
	#
	#
	# parses the packet from the raw data from ThreadedRead
	#
	
	#    Packet Format
	#	first byte is header will be "J" if internal sizes are uint16 and "K" if internal sizes are uint32
	# 	most packets will be uint16 unless they contain really large structures like images which wont be
	# 	often received by the interface, mostly sent by interfaces that are also video sources
	#
	#	if type J the next 2 bytes are the total size of the packet as uint16
	#	if type K the next 4 bytes are the total size of the packet as uint32
	#
	#   then begin key/value pairs, read to the end of the packet
	#		keys are always 4 bytes
	#		size of value string, if J is a uint16 if K then uint32
	#		then the value data
	#		repeat until you run out of data
	#
	
	def _parse( self, rawData):

		
		if isPy3:
			input = BytesIO( rawData)
		else:
			input = io.BytesIO( rawData)
		
		packetHeader = input.read( 1)
		if packetHeader == b"J":
			packetSize = unpack( "H", input.read( 2))[0]
		elif packetHeader == b"K":
			packetSize = unpack( "I", input.read( 4))[0]
		else:
			print( "XTCommand._parse: unknown packet header (%s)" % packetHeader )
			return False
			

		# the next bit is flags and technically tells us if the data in the packet is little endian or not
		# this is left over from when we were supporting both PPC and Intel based macs. All data at the moment
		# is from the same CPU so this should not ever be necessary
		
		packetFlag = input.read( 1)
		
		# now loop and get the key value 
		
		while True:
			if isPy3:
				# keys should always be strings, so decode to an str
				thisKey = input.read( 4).decode()
			else:
				# python 2.7 will just use the str returned from the read method
				thisKey = input.read( 4)
			
			# this will return an empty string upon EOF
			if len( thisKey) == 0:
				break
			
			
			#
			#	two different value headers for 2 different size fields
			if packetHeader == b'J':
				thisDataSize = unpack( "H", input.read( 2))[0]
			elif packetHeader ==b'K':
				thisDataSize = unpack( "I", input.read( 4))[0]
			else:
				# this should not happen as the header is pre-validated before calling this
				return( False)
			
			#
			# no post processing on values in either python type
			# values are left as bytes like objects in py3 and raw str types in py2
			self.values[ thisKey] = input.read( thisDataSize)
				
		
		input.close()
		self.isValid = True

		
		return True
		
	
	
	
	
	
	
	
	
	#
	#  	X T D A T A   
	#
	#  all dictionaries of information sent back and forth to XTension 
	#  that are not just commands are sent via this class.
	#  it provides a python dictionary like interface for embedded xtData classes
	#  and the ability to flatten it for sending over the connection to XTension
	#
	
	
		
class xtData:
	
	kTrue = 'True'
	kFalse = 'False'
	
	kBinaryDoneHeader = b'E' #chr( 69)
	kBinaryHeaderLabel = b'Xbdb'
	kBinaryObjectHeader = b'O'#chr( 79)
	kBinaryPictureHeader = b'F'#chr( 70)
	kBinaryStringVersion = b'A'#chr( 65)
	kBinaryValueHeader = b'V'#chr( 86)
	
	kNamedTypePrefix = '_typ_'
	kNamedTypeUUID = '_typeuuid_'
	

	kNamedTypeBinary = b'bin'
	kNamedTypeBoolean = b'boo'
	kNamedTypeColor = b'col'
	kNamedTypeDate = b'dte'
	kNamedTypeDouble = b'dou'
	kNamedTypeFile = b'fil'
	kNamedTypeInteger = b'int'
	kNamedTypeString = b'str'
	#kRawPictureDataPrefix = b'_rawpic_'	# this is no longer used in anything at the moment
	
	
	#
	# initialData can be left out in which case an empty
	# xtdata object is created.
	# if the passed value is a string it must be in the xtData binary format as received
	# from XTension. You might get this from a command.
	# the most common way to get an xtData structure is in the xtKeyData value of a command
	# if thats the case then you can pass the command to initialData and that value will be
	# used if there to setup the object.
	#
	def __init__(self, initialData=None):
		self.containers = []
		self.hasChanges = False
		self.name = ''
		self.subscribedToAll = []
		self.subscribers = {}
		self.subscribedToChildren = {}
		self.uuid = 0
		self.values = {}
		self.parent = None
		
		# added ability to send all the changes to a subscriber as one list
		# so that you dont have to do hacks like creating a callback thread to see what
		# all the values are and so forth. So in these cases all the changes that are received will
		# be sent to the subscriber as a list of key, value pairs like:
		# def allChangesAsListCallback( changedData):
		#	changedData = [ [key, value], [key, value]] for however many have changed
		#
		# this is ONLY sent in response to a merge from changes in XTension and not
		# if you make local changes though. Those are still strictly handled by the original 
		# hooks into get/set
		
		self.subscribedByList = {}
		
		
		
		if initialData:
			workData = ''
			if isinstance( initialData, str):
				workData = initialData
			elif isinstance( initialData, XTCommand):
				workData = initialData.getBytes( xtKeyData) # use get bytes to parse the non-converted data, not utf8!
		
			if not workData == '':
				self._parse( workData)
	#
	#	string conversion handler provides the raw encoded data for setting to 
	# 	a command object.
	def __str__( self):
		return self.save()
		
	#
	def __getitem__( self, key):
		return self.get( key)
			
	def __setitem__( self, key, value):
		self.set( key, value)
		
	def __len__( self):
		return len( self.values)
		
		
		
	#
	#	GET BYTES
	#
	#	Python3 helper, returns the value as a byte like object which is what it's actually 
	#	stored as internally without doing the conversion. For some comparisons and such this
	#	may be preferable and faster than converting it to a python primitive and then 
	#	turning it back into a byte like object or something silly like that.
	#	in that case use getBytes
	# 
		
	def getBytes( self, key, default=None):
	
	
		if type( key) == tuple:
			default = key[1]
			key = key[0]
			
		if type( key) == list:
			theReply = []
			for workItem in key:
				theReply.append( self.get( workItem))
				
			return theReply
		
		if isPy3 and type( key) == bytes:
			key = key.decode()
			
		if key not in self.values:
			return( default)
			
		return( self.values[key])
		
	#
	#	can pass a single key and a default
	# 	or you can pass an array of keys to get an array of values back
	#	or you can pass an array of tuples with key, default in them like
	#	thing1, thing2 = data.get( [('key', 'default'), ('key', 'default')])
	#	that is entirely untested at the moment though. good for when you'd otherwise
	#	have to make multiple calls to get.
	#
	
	# note that internally all values are stored as byte like objects on py3
	# and str type on py2 so decoding is necessary on py3 before we cast as other types
	#
	def get( self, key, default=None):
	
		# can pass (key, default) as a tuple
		# or a list of them see below
		if type( key) == tuple:
			default = key[1]
			key = key[0]
			
		# if passing a list you can pass either a list of keys
		# and get None as the value if the key doesn't exist or
		# you can pass a list of tuples with the second value being the
		# default like: [(key1, default1), (key2, default2), key3, (key4, default4), etc...]
		if type( key) == list:
			theReply = []
			
			for workItem in key:
				theReply.append( self.get( workItem))
				
			return theReply

			
	
		# unnecessary idiot check to make sure the key is a string
		if isPy3 and type( key) == bytes:
			key = key.decode()
		

		# return default if the key is not in our values object
		if key not in self.values:
			return( default)


		
		# if requesting the uniqueID then always return it as a string
		if key == xtUnitKeyUniqueId:
			if isPy3:
				return self.values[ xtUnitKeyUniqueId].decode()
			else:
				return self.values[ xtUnitKeyUniqueId]
			
		
		intType = None # for converting to the proper type
		
		if (self.kNamedTypePrefix + key) in self.values:
			#we have a type stored in the value dict so use that to type it and return the correct type
			intType = self.values[ self.kNamedTypePrefix + key]
			
			if isPy3 and type( intType) == bytes:
				intType = intType.decode()

		else:
			intType = None # just return whatever it is, probably a string, if this is the case _typeuuid_ 
			
			
		#
		#	BINARY TYPE
		#	
		# handled first because we don't want to decode the bytes like object in py3
		#
		
		if intType == self.kNamedTypeBinary:
			return( self.values[ key])
			
		# get the value and convert to str type for python 3
		workValue = self.values[ key]		
		try:
			workValue = workValue.decode()
		except:
			pass
			
		#
		#	STRING TYPE
		#
		if intType == None or intType == self.kNamedTypeString:
		

			if isPy3:
				return( workValue) # already converted from bytes like object
				
			# py2.7 need to return a unicode string
			#return( self.values[ key].encode( 'utf-8'))
			
			workValue = self.values[ key]
			
			if type( workValue) != unicode:
				return unicode( workValue, 'utf-8')
			else:
				return workValue
			

		#
		#	BOOLEAN TYPE
		#
		elif intType == self.kNamedTypeBoolean:
				
			if workValue == self.kTrue or workValue == 'true': #why it is sometimes lower case dont know
				return True
			else:
				return False


		#
		#	COLOR TYPE
		#
		#	returns a tuple with RGB values in it
		#
		elif intType == self.kNamedTypeColor:			
				
			return workValue.split( ',')
			
			
		#
		#	DATE TYPE
		#
			
		elif intType == self.kNamedTypeDate:
			# dates in XTension data containers are stored as a string
			# month/day/year hour:min:second
			# with always a 4 digit year and a 24 hour clock
			#
			
				
			datePart, timePart = workValue.split( " ", 1)
			dateMonth, dateDay, dateYear = datePart.split( "/", 2)
			timeHours, timeMinutes, timeSeconds = timePart.split( ":", 2)

			return datetime( int( dateYear), int( dateMonth), int( dateDay), int( timeHours), int( timeMinutes), int( timeSeconds), 0, None)
			
			
		#
		#	DOUBLE TYPE (really a float)

		elif intType == self.kNamedTypeDouble:
		
			# there is a problem with localization where if you had a comma inserted at the end of this
			# then it will not be able t turn it into a float without an error
			# so in this case we're going to filter for that
			# the new xtFloat class handles that
			#
			return( xtFloat( workValue))

		elif intType == self.kNamedTypeInteger:
			# the strings from XTension come with a decimal at the end which has to be removed
			# before we can convert it to an int() in python. It otherwise chokes on it even though
			# it never has anything after the decimal point.
			# created the new xtInt command to parse it properly.
				
			return( xtInt( workValue))
			#return int( workValue)
		else:
			
			# don't know what it is, return the raw string 
			
			
			
			return( workValue)
	
	
	
	
	
	
	
	
	#
	#		SET
	#
	#	pass suppressNotifications=True to keep subscribers from being notified
	#
	def set( self, key, value, **kwargs):
		
		typeKey = self.kNamedTypePrefix + key
		typeVal = self.kNamedTypeString
		adjustedVal = value		


		# 
		#	INTEGER TYPE
		#
		if type( value) == int:
			typeVal = self.kNamedTypeInteger
			adjustedVal = str( value)
			
		#
		#	FLOAT TYPE (really double)
		#
		elif type( value) == float:
			typeVal = self.kNamedTypeDouble
			# doubles limited to 4 decimal places here? Might want more?
			# this should not be affected by localization as we're specifically setting the period
			adjustedVal = "{:+.4f}".format( value)


		#
		#	DATE TYPE
		#
		# changed to just importing datetime from datetime and not the entire module
		# which means we have a type that is datetime and not an instance
		# elif isinstance( value, datetime): # or isinstance( value, datetime.datetime):
		elif type( value) == datetime:
			typeVal = self.kNamedTypeDate
			#adjustedVal = str( value.month) + "/" + str( value.day) + "/" + str( value.year) + " " + str( value.hour) + ":" + str( value.minute) + ":" + str( value.second)			

			adjustedVal = str( value.month) + "/" + str( value.day) + "/" + str( value.year) + " " + str( value.hour) + ":" + str( value.minute) + ":" + str( value.second)			
				
				

		#
		#	BOOLEAN TYPE
		#
		elif type( value) == bool:
			typeVal = self.kNamedTypeBoolean

			if value == True:
				adjustedVal = self.kTrue
			else:
				adjustedVal = self.kFalse
				

		#
		#	STR TYPE
		#
		# no unicode impact here, setting a string is perfectly valid and how we would set a binary object anyway
		
		elif type( value) == str:
			typeVal = self.kNamedTypeString
			adjustedVal = value

		#
		#	COLOR TYPE
		#
		#	color is sent as a 3 value tuple for R,G,B
		elif type( value) == tuple or type( value) == list:
			typeVal = self.kNamedTypeColor
							
			adjustedVal = []
			for i in value:
				if isPy3 and type( i) == bytes:
					i = i.decode()
				
				# DANGEROUS what if somebody passes unicode strings in the tuple of RGB values?
				if type( i) != str:
					i = str( i)
					
				adjustedVal.append( i)
				
			adjustedVal = ",".join( adjustedVal)
			
			
		#
		#	BINARY TYPE
		#
		elif type( value) == bytes:
			typeVal = self.kNamedTypeBinary
			adjustedVal = value
			
		#
		#	UNICODE
		#
		elif not isPy3 and type( value) == unicode:
			typeVal = self.kNamedTypeString
			adjustedVal = value
			
			
		else:
			XTension.writeLog( "unsupported variable type, cannot store %s=%s(%s)" % (key, value, type(value)), xtLogRed)
			return
			
		#XTension.writeLog( "in set with key=" + key + " typeval=" + typeVal ) #+ " adjusted=" + adjustedVal)
			
		self.values[ typeKey] = typeVal
		
		# check to see if we need to do notifications for a change
		# if changing things in the local dictionary in order to not get a notification
		# again when the value is updated by XTension you can pass 
		# suppressNotifications=True to the set method
		#  			
		
		if not kwargs.get( 'suppressNotifications', False):
			if not key in self.values:
				self.subscribersNotify( key, value)
			#elif self.values[ key] != value:
			#elif self.get( key) != value:
			elif self.get( key) != adjustedVal: # use the adjusted value!
				#XTension.writeLog( "notify subscribers for key=%s" % key)
				self.subscribersNotify( key, value)
			
		#
		# all values must be byte like objects on Py3
		#
		if isPy3 and type( adjustedVal) != bytes:
			adjustedVal = adjustedVal.encode()
		
		# finally put the value into our dictionary object
		self.values[ key] = adjustedVal
	
	
	
	
	
	#
	# 	EXISTS
	#
	def exists( self, key):
		if isPy3 and type( key) == bytes:
			key = key.decode()
			
		return( key in self.values)
		
		
		
	#
	#	INSERT CONTAINER
	#
	def insertContainer( self, newContainer):
	
		#XTension.writeLog( "newcontainer.uuid=%s" % newContainer.uuid, xtLogGreen)

		# inserted containers must have a UUID in order to properly sync
		if newContainer.uuid == 0:
			newContainer.uuid = str( uuid.uuid4())
			newContainer.values[ self.kNamedTypeUUID] = newContainer.uuid
			
		newContainer.parent = self
		self.containers.append( newContainer)
		#self.subscribersNotify( newContainer.name, newContainer)
		self.notifyChildrenSubscribers( newContainer, False)
				
	
	
	#
	#	GET CONTAINER
	#
	
	def getContainer( self, key, index):
		
		count = 0
		for x in self.containers:
			if x.name == key:
				count += 1
				
			if count == index:
				return( x)
				
		return( None)
		
	#
	#	GET CONTAINER COUNT
	#
		
	def getContainerCount( self, key):
		count = 0
		for x in self.containers:
			if x.name == key:
				count += 1
			
		return( count)
	
	
	#
	#	GET ALL CONTAINERS
	#
	#	that contain a specific key
	#
	def getAllContainers( self, key):
		work = []
		for x in self.containers:
			if x.name == key:
				work.append( x)
			
		return( work)
	
	#
	#	CONTAINERS WITH VALUE
	#
	#	all the containers where a specific key is equal to a specific value
	#
	def containersWithValue( self, containerKey, keyToCompare, value):
		work = []
		for x in self.containers:
			if x.name == containerKey or containerKey == "*":
				if x.get( keyToCompare) == value:
					work.append( x)
					
		return( work)
		
	#
	#	CONTAINER BY UUID
	#
	# used by the merge function to find the specific container object that
	# the merge data is for.
	#
	def containerByUUID( self, theUUID):
		for x in self.containers:
			if x.uuid == theUUID:


				return x
	
	
	#
	#	SUBSCRIBE TO CHILDREN
	#
	#	this is for syncing different xData object back to XTension like in the 
	#	interface configuration for the new web interface that needs to be able to create
	#	it's own configuration and save it to XTension.
	
	def subscribeToChildren( self, subscriber, tag=None):
		self.subscribedToChildren[ subscriber] = tag
	
	#
	#	UNSUBSCRIBE TO CHILDREN
	#	see above
	#
	def unsubscribeToChildren( self, subscriber):
		if subscriber in self.subscribedToChildren:
			del( self.subscribedToChildren)
			
	#
	#	HAS CHILD SUBSCRIBERS
	#
	#	called by our chilren when values change to find out if they should bother to 
	#	create the sync objects and pass them upstream. If we have any child subscribers then
	#	we return true. If we do not but we have a parent reference we call that recursively and
	#	return the result upstream. If we do not and also if we do not have a parent meaning that 
	#	we are the root object then we return false.
	#
	
	def hasChildrenSubscribers( self):
		# if we have child subscribers then return true
		if len( self.subscribedToChildren) > 0:
			return True
		
		# if we do not have a parent and no subscribers then false
		if self.parent == None:
			return False
		
		# if we do have a parent, but no subscribers ourselves then pass it downstream
		return self.parent.hasChildSubscribers()
		
			
	
	
	
	#
	#	SUBSCRIBE FOR LIST
	#
	#	returns all the changes in the merge in a single list of [key, value] tuples or lists
	# 	see discussion in __init__ for this class for more info
	#
	
	def subscribeForList( self, keys, subscriber, tag=None):
		# make sure the type of keys is iterable even if there is only one
		# this way you can subscribe with a single string item
		# or a list of many
		if type( keys) != list and type( keys) != tuple:
			keys = [keys]
			
		for thisKey in keys:
			if not thisKey in self.subscribedByList:
				self.subscribedByList[ thisKey] = [(subscriber, tag)]
			else:
				current = self.subscribeByList[ thisKey]
				currentIndex = self.leftIndexOf( current, subscriber)
				
				if currentIndex == -1:
					current.append(  (subscriber, tag))
				else:
					current[ currentIndex] = (subscriber, tag)
					
	#
	#	UNSUBSCRIBE FOR LIST
	#
	
	def unsubscribeForList( self, keys, subscriber):
		if type( keys) != list and type( keys) != tuple:
			key = [keys]
			
		for thisKey in keys:
			if not thisKey in self.subscribedByList:
				# no one is subscribed for that key
				continue
			
			current = self.subscribedByList
			currentIndex = self.leftIndexOf( current, subscriber)
			
			if currentIndex == -1:
				# this subscriber is not subscribed to this key
				continue
				
			del( current[ currentIndex])
			# and if that is the last person subscribed to this key
			# then also remove the entire key entry
			if len( current) == 0:
				del( self.subscribedByList)


	#
	#	UNSUBSCRIBE
	#
	def unsubscribe( self, keys, subscriber):
	
		# keys must be either a string or an array of strings
		# should probably handle the eventuality that someone passes
		# bytes here in python3?
		
		#if type( keys) == str:
		# in python3 it might be unicode or byte like objects or anythign
		# so instead of comparing to string check against iterable types
		if type( keys) != list and type( keys) != tuple:
			keys = [keys]
		
		
		for thisKey in keys:
			if not thisKey in self.subscribers:
				# nothing actually subscribed for this
				continue
			
			current = self.subscribers[ thisKey]
			currentIndex = self.leftIndexOf( current, subscriber)
			
			if currentIndex > -1:
				del( current[ currentIndex])
				# and if there are no more subscribers to this key then remove it from our 
				# higher subscribers index
				if len( current) == 0:
					del( self.subscribers[ thisKey])
				
		
		
				
	#
	#	SUBSCRIBE
	#
	#	subscribe to changes for a list of keys. Will callback when any of them change
	#	callback function should have 4 parameters, theKey, theValue, theTag, theData
	#	where theKey and theValue are self explanatory
	#	theTag is whatever variable you passed for the tag below, it is just saved and returned
	# 	to you. theData is a reference to this data class so that you could find other
	#	values in it to test against 
	# 	note that the data object itself is not updated when the callbacks are made so that
	#	you can compare the passed theValue against what it currently in the dictionary if you need
	#	to know what the previous value was. Once all callbacks have completed then the 
	#	actual values in the object will be updated.
	#
	def subscribe( self, keys, subscriber, tag=None):
		
		# OK to pass a single key as just a string and not as an array now
		#if type( keys) == str:
		# in python3 it might be unicode or byte like objects or anythign
		# so instead of comparing to string check against iterable types
		if type( keys) != list and type( keys) != tuple:
			keys = [keys]
			
		for thisKey in keys:
		
			if not thisKey in self.subscribers:
				self.subscribers[ thisKey] = [(subscriber, tag)]
			else:
				current = self.subscribers[ thisKey]
				currentIndex = self.leftIndexOf( current, subscriber)
				
				if currentIndex == -1:
					current.append( (subscriber,tag))
				else:
					current[ currentIndex] = (subscriber, tag)
	
	#
	#	SUBSCRIBE TO ALL
	#
	# gets you the callback for any and all updates to the data structure
	#
	def subscribeToAll( self, subscriber, tag=None):
		index = self.leftIndexOf( self.subscribedToAll, subscriber)
		
		if index == -1:
			self.subscribedToAll.append( (subscriber, tag))
		else:
			self.subscribedToAll[ index] = (subscriber, tag)
			
	#
	#	UNSUBSCRIBE FROM ALL
	#
	def unsubscribeFromAll( self, subscriber):
		index = self.leftIndexOf( self.subscribedToAll, subscriber)
		
		if index > -1:
			del( self.subscribedToAll[ index])
	
	#
	#	SUBSCRIBERS FORCE
	#
	#	updates all subscribers even if the value hasn't changed
	#
	def subscribersForce( self, theKey):
		if theKey in self.subscribers:
			self.subscribersNotify( theKey, self.values[ theKey])
	
	
	#
	# the callback must have the following parameters
	# valueChanged( theKey, theValue, theTag, theData)
	# where theData is a reference to this object that is calling it
	#
	def subscribersNotify( self, theKey, theValue):
		for x in self.subscribedToAll:
			theCallback, theTag = x
			theCallback( theKey, theValue, theTag, self)
			
		if theKey in self.subscribers:
			work = self.subscribers[ theKey]
			for x in work:
				theCallback, theTag = x
				theCallback( theKey, theValue, theTag, self)
		
		# now look for any children subscribers if we are not the root of the thing			
			
		if self.parent != None and self.hasChildrenSubscribers:
			newData = xtData()
			newData.uuid = self.uuid
			newData.values[ self.kNamedTypeUUID] = self.uuid
			
			# if we are removed then theValue will be None and we need to add instead
			# the special removed command in order to sync
			
			if not theValue:
				theValue = b"_del_"
			
			newData.set( theKey, theValue)
			self.parent.notifyChildrenSubscribers( newData, False)
			
				
	def notifyChildrenSubscribers( self, newData, isRemoved):
	
		if len( self.subscribedToChildren) == 0 and self.parent == None:
			# nobody subscribed and no parent to pass it down to, nothing to do
			return
			
		
		x = xtData()
		x.uuid = self.uuid
		x.set( self.kNamedTypeUUID, self.uuid)
		x.insertContainer( newData)
		
		for p in self.subscribedToChildren:
			p( x, isRemoved)
		
		if self.parent != None:
			self.parent.notifyChildrenSubscribers( x, False)

		
		
		
		
		
		
		
		
		
		
				
				
	def leftIndexOf( self, current, value):
		index = 0
		for x in current:
			part1, part2 = x
			if part1 == value:
				return index
			index += 1
		
		return -1
		
		
	def remove( self, key):
		if key in self.values:
			#self.values.remove[ key]
			del( self.values[ key])
			
			# also remove the type string
			
			workType = self.kNamedTypePrefix + key
			if workType in self.values:
				del( self.values[ workType])

			self.subscribersNotify( key, None)
	
	
	
	#
	#	M E R G E
	#
	#	called when new data is received for this object from XTension 
	#	the data sets will be conformed removing any
	#	added ability to send all the changes subscribed at once
	#
		
			
	def merge( self, newData):
		#if the item has been removed then we will send the value will be
		# "_del_" and we can remove that item and send the update with the
		# value being None
		#XTension.debugLog( "begin data merge")
		# first merge or add any key=value pairs
		
		# added sending all the changes as one list
		# structure of this item is keyed by subscriber which will then
		# build up a list of items so like:
		# { callback:[ (key, value, tag), (key, value, tag), ...], ...}
		
		# then below processing they will all be sent after the changes are applied
		changesAsList = {}
		# should we actually add the value or not

		
		for key, value in newData.values.items():
			#XTension.writeLog( "MERGE: key=%s(%s) value=%s(%s)" % ( key, str( type( key)), value, str( type( value))))
			valueHasChanged = False		
			#look for deleted values
			try:
				if value == b"_del_":
					if key in self.values:
						del( self.values[ key])
						value = None
						self.subscribersNotify( key, None)
						valueHasChanged = True
				else:		
					#only do this if it's not a type entry
					if key[:len( self.kNamedTypePrefix)] != self.kNamedTypePrefix:
						# XTension 1005 changed this to use the cast or properly typed objects
						# from the get commands rather than try to compare the root strings
						# as sometimes they may contain non ascii chars if they are unicode in which
						# case we would get an error below
						# by comparing the return from the .get method we make sure that they are cast to 
						# unicode strings in that case
						currentValue = self.get( key)
						newValue = newData.get( key)
						
						if (not key in self.values) or (currentValue != newValue):
							self.set( key, newData.get( key)) #use the get so that the type is set and carried forward
							valueHasChanged = True
		
# 						elif currentValue != newValue:
# 							self.set( key, newData.get( key)) #use the get so that the type is set and carried forward	self.set( key, value)
# 							#self.set( key, newValue) #use the get so that the type is set and carried forward	self.set( key, value)
							
				# now build the structure for subscribedByList
				# using the changesAsList object to hold all the references as described above
				
				
				if valueHasChanged and (key in self.subscribedByList):
					workArray = self.subscribedByList[ key]
					for x in workArray:
						(thisCallback, thisTag) = x
						
						if not thisCallback in changesAsList:
							changesAsList[ thisCallback] = [(key, value, thisTag)]
						else:
							changesAsList[ thisCallback].append( (key, value, thisTag))


			except Exception as e:
				XTension.writeLog( "error in data.merge key=%s value=%s error=%s" % (key, value, e), xtLogRed)
				#XTension.writeLog( "error in data.merge key=" +  key + " value=" + value + " error=" + str( e), xtLogRed)
				# above line removed because it cannot concatenate if it is a bytes like object, but the format command can insert it no problem.
				# though it will be in the output format of b'thing' which is fine and gives more debugging info anyway
				XTension.writeLog( traceback.format_exc(), xtLogRed)


		# now outside the loop of processing the merge we send any subscribedAsList people that might be there
		# walk the index we created and call them all in one go
		
		for workCallback in changesAsList:
			workList = changesAsList[ workCallback]
			try:
				workCallback( workList, self)
			except Exception as e:
				XTension.writeLog( "Error in changesAsList callback handling: %s" % e, xtLogRed)
				XTension.writeLog( "debug: changes as list=%s" % changesAsList, xtLogRed)

		
		# now merge any embedded objects
		# no way to delete a container yet by merging though... TODO
		for newContainer in newData.containers:
			foundContainer = self.containerByUUID( newContainer.uuid)
			if foundContainer == None:
				self.insertContainer( newContainer)
				self.subscribersNotify( newContainer.name, newContainer)
			else:
				foundContainer.merge( newContainer)
		
	#
	#	DEBUG LOG
	#	_DEBUG LOG
	#
	#	also registered as just debugLog without the underscore because it is silly this way
	#	I originally considered this a private debugging call for myself but it is so useful
	#	for just seeing what is in things like script dataParms that are passed to you that
	#	I'm also exposing it as just debugLog but cannot remove the underscore version
	#	since that is in use in many plugins already. But it is deprecated please use the
	#	non underscore version going for new development.
	#
	#
	# dumps the entire contents of the data object to the XTension log
	# so you can see whats really here to ease debugging
	#
	
	def debugLog( self, indent=0):
		self._debugLog( indent)
	
	def _debugLog( self, indent=0):
		indentString = ''.ljust( indent * 5)
		for key, var in self.values.items():

			# don't write the type entries
			#if key[:5] != self.kNamedTypePrefix:
			# or rather do because I now want to see them...
			XTension.writeLog( "%s %s(%s)=%s(%s)" % (indentString, key, type( key), var, type( var)))


			
		XTension.writeLog( indentString + "-----container count: " + str( len( self.containers)))
		
		indent += 1
		for x in self.containers:
			
			XTension.writeLog( indentString + ">>>Container Name:" + x.name)
			x._debugLog( indent)

			
	#
	#	SAVE
	#
	# saves the data object to a BytesIO stream and returns it
	#
	def save( self):
		output = io.BytesIO()
		self._saveToString( output)
		finished = output.getvalue()
		output.close()
		return finished
	
	#
	#	_SAVE TO STRING
	#
	# pass an already created io.BytesIO() stream to have this written to
	# yes it's not a string, but it's the same name as the call inside XTension where it is
	# so for my own sanity I called it the same thing.
	#
	def _saveToString( self, output):
		output.write( self.kBinaryHeaderLabel)
		output.write( self.kBinaryStringVersion)
		output.write( pack( "B", 76))
		output.write( b'  ')
		
		for key in self.values.keys():
			value = self.values[ key]
			output.write( self.kBinaryValueHeader)
			output.write( pack( "I", len( key)))
			output.write( bytearray( key, "utf-8"))
			output.write( pack( "I", len( value)))

			if type( value) == str:
				value = bytearray( value, "utf-8")
				
			output.write( value)
			
		for container in self.containers:
			output.write( self.kBinaryObjectHeader)
			output.write( pack( "I", len( container.name)))
			if type( container.name) in [bytes, bytearray]:
				output.write( container.name)
			else:
				output.write( bytearray( container.name, 'utf-8'))
				
			container._saveToString( output)
			
		output.write( self.kBinaryDoneHeader)
		
		
	#
	#	G E T   O B J E C T    S A F E
	#
	# used when you need a native object safe value for dumping to json
	# or other primitive type. Will return only strings, integers, floats and booleans
	# no complex types for dates or colors, those will stay as strings to be handled
	# by the remote object
	#
	def getObjectSafe( self, key, default=None):
		
		if key not in self.values:
			return default
		
		intType = self.kNamedTypeString
		if (self.kNamedTypePrefix + key) in self.values:
			intType = self.values[ self.kNamedTypePrefix + key]
			
		if intType == self.kNamedTypeBoolean:
			if self.values [key] == self.kTrue or self.values[ key] == 'true':
				return True
			else:
				return False
		
		
		elif intType == self.kNamedTypeDouble:
			return xtFloat( self.values[ key])
			
			
		elif intType == self.kNamedTypeInteger:
			return int( self.values[ key])

		elif intType == self.kNamedTypeDate:
			workDate = self.get( key)
			return self.get( key).isoformat()
			
		else:
			return self.values[ key]
			
	# MAKE PRIMITIVE
	def makePrimitive( self, value):
		if type( value) == int:
			return value
		elif type( value) == float:
			return value
		elif type( value) == str:
			return value
		elif type( value) == unicode:
			return value
		elif type( value) == bool:
			return value
		elif type( value) == list:
			return ",".join( value)
		elif type( value) == tuple:
			return ",".join( value)
		elif type( value) == datetime:
			return value.isoformat()
		else:
			XTension.writeLog( "unknown variable type in makePrimitive: (%s) type( %s)" % ( value, type( value)), xtLogRed)
			return value

		
	
		
		

	#
	#  	C L O N E   A S   O B J E C T
	#
	#	returns an object that is suitable for converting to JSON
	# 	simple types like numbers and booleans and strings are 
	#	converted but other types are left as strings, dates and colors.
	#
	#	Filter types can be set to True if you do not want the descriptor values
	#	that tell you what the other values type is.
	#
	def cloneAsObject( self, filterTypes = False):
		XTension.debugLog( "begin cloneAsObject")
		o = {}
		

		
		for thisKey in self.values:
			#XTension.writeLog( thisKey + "=" + self.values[ thisKey])
			
			# we want the unique id to always be a string even if it comes across as an integer
			# so do a pre-check for that and always get it as a string
			if thisKey == xtUnitKeyUniqueId:
				o[ thisKey] = self.get( xtUnitKeyUniqueId)
				continue
				
			
			intType = self.kNamedTypeString			
			try:
				#XTension.writeLog( "key=(%s) key[5:]=(%s)" % (thisKey, thisKey[:5]))
				if thisKey[:5] == self.kNamedTypePrefix:
					#XTension.writeLog( "found a prefix (%s) compared to(%s)" % (thisKey, thisKey[:5]))
					if not filterTypes:
						o[ thisKey] = self.values[ thisKey]
					#XTension.writeLog( "prefix sent about to continue")
					continue
				
				elif (self.kNamedTypePrefix + thisKey) in self.values:
					#XTension.writeLog( "part 2")
					#XTension.writeLog( "found named prefix (%s)" % (self.kNamedTypePrefix + thisKey))
					intType = self.values[ self.kNamedTypePrefix + thisKey]
			
			except Exception as e:
				XTension.writeLog( "first part exception (" + str( e) + ")", xtLogRed)
			
			XTension.debugLog( "intType=%s for key %s" % (intType, thisKey))
			
			try:
				if intType == self.kNamedTypeBoolean:
					try:
						if self.values[ thisKey] == self.kTrue or self.values[ thisKey] == 'true':
							o[ thisKey] = True
						else:
							o[ thisKey] = False
					except Exception as e:
						XTension.writeLog( "second part 1 (" + str( e) + ")")
						
				elif intType == self.kNamedTypeDouble:
					try:
						o[ thisKey] = xtFloat( self.values[ thisKey])
					except Exception as e:
						XTension.writeLog( "second part 2 (" + str( e) + ")")
						
						
				elif intType == self.kNamedTypeInteger:
					try:
						o[ thisKey] = int( self.values[ thisKey])
					except Exception as e:
						XTension.writeLog( "second part 3 (" + str( e) + ")")

				elif intType == self.kNamedTypeDate:
					o[ thisKey] = self.makePrimitive( self.get( thisKey))
					
				# attempt to force things to be strings as well
				elif intType == self.kNamedTypeString:
					XTension.debugLog( "converting from string for key (%s)" % thisKey)
					x = self.values[ thisKey]
					if type( x) == bytes:
						XTension.debugLog( "it was found to be bytes!")
						o[ thisKey] = x.decode( 'utf-8')
					else:
						XTension.debugLog( "it was NOT bytes")
						o[ thisKey] == x

						
				else:
					try:
						o[ thisKey] = self.values[ thisKey]
					except Exception as e:
						XTension.writeLog( "second part 4 (" + str( e) + ")")
						
			except Exception as e:
				#XTension.writeLog( "exception in loop key=" + thisKey + " intType=" + intType + " (" + str( e) + ")", xtLogRed)
				XTension.writeLog( "exception in cloneAsObject key=%s (%s) intType=%s err=%s" % (thisKey, type( thisKey), intType, e), xtLogRed)
				XTension.writeLog( traceback.format_exc(), xtLogRed)
				
		# now convert any containers
		
		if len( self.containers) > 0:
			o['containers'] = {}
		
			for thisContainer in self.containers:
				if thisContainer.name in o['containers']:
					o['containers'][thisContainer.name].append( thisContainer.cloneAsObject())
				else:
					o['containers'][thisContainer.name] = [ thisContainer.cloneAsObject()]
				
		return o
				
		
	

	#
	#	_PARSE
	#
	# parses either a string or an existing BytesIO object containing the binary
	# data representation as it's send from XTension
	#
	def _parse( self, rawinput):


		if isinstance( rawinput, io.BytesIO):
			input = rawinput
		else:
			input = io.BytesIO( rawinput)
			
		
		if input.read( 4) != self.kBinaryHeaderLabel:
			XTension.writeLog( "unable to parse xtData object, bad header", xtLogRed)
			return( False)
			
		protocolVersion = input.read( 1) #unpack( "B", input.read( 1))[0]
				
		if protocolVersion != self.kBinaryStringVersion:
			XTension.writeLog( "protocol version incompatible with xtData class version", xtLogRed)
			return( False)
		
		#
		# this is leftover from when we were supporting talking between PPC and Intel machines
		# it will now just always be the CPU format which is the same everywhere we run right now
		#
		byteOrder = unpack( "B", input.read( 1))
			
		# skip 2 bytes for future expansion
		input.read( 2)
		
		while True:
			thisHeader = input.read( 1)
			if thisHeader == '':
				#EOF
				return( True)
				
			#
			# this object is done loading return the stream to the parent object, if any
			#
			elif thisHeader == self.kBinaryDoneHeader:
				return( True)
				
			#
			# the next structure is a key=value pair
			#
			elif thisHeader == self.kBinaryValueHeader:
				thisKey = input.read( unpack( "I", input.read( 4))[0])
				
				# keys are strings always
				if isPy3 and type( thisKey) == bytes:
					thisKey = thisKey.decode()
				
				#XTension.writeLog( "about to read value for key %s" % thisKey)
				thisValue = input.read( unpack( "I", input.read( 4))[0])
				#XTension.writeLog( "read value of %s" % thisValue)
				
				if thisValue == '':
					continue
				
					
				if thisKey == self.kNamedTypeUUID:
					self.uuid = thisValue.decode()
					
				self.values[ thisKey] = thisValue
					
			#
			# the next structure is an embedded named xtData object
			#
			elif thisHeader == self.kBinaryObjectHeader:
			
				newData = xtData()
				newData.name = input.read( unpack( "I", input.read( 4))[0])
				
				if isPy3 and type( newData.name) == bytes:
					newData.name = newData.name.decode()
				
				newData.parent = self
				self.containers.append( newData)
				newData._parse( input)
				


	

#
#	X T    S H A R E D   O B J E C T
#
# parent class for all shared objects with XTension
# provides basic functionality for handling events and subscribing
#

class XTSharedObject:
	def __init__( self, theData):
		self.data = theData
		

		self.name = theData.get( xtUnitKeyName)
		# the .get for an xtUnitKeyUniqueId forces it to just be returned as a string
		self.uniqueId = theData.get( xtUnitKeyUniqueId)
	
		self._commandHandlers = {}
		self._scriptHandlers = {}
		
		
	#
	#	ADD COMMAND HANDLER
	#
	# if you need to handle a command register for the command type using this command
	# the command will be passed to your callback as the only parameter
	#
	# updated to be able to pass a list of command codes to assign to a single callback
	#
	def addCommandHandler( self, commandCode, theCallback):	
	
		if type( commandCode) != list:
			commandCode = [commandCode]
			
		for thisCode in commandCode:
			if not thisCode in self._commandHandlers:
				self._commandHandlers[ thisCode] = [theCallback]
			else:
				self._commandHandlers[ thisCode].append( theCallback)
	
	#
	#	REMOVE COMMAND HANDLER
	#
	#	added ability to pass a list of commandCodes to remove
	#
	def removeCommandHandler( self, commandCode, theCallback):
	
	
		if type( commandCode) != list:
			commandCode = [commandCode]
			
		for thisCode in commandCode:	
			if thisCode in self._commandHandlers:
				self._commandHandlers[ thisCode].remove( theCallback)
			
	
	#
	#	ADD SCRIPT HANDLER
	#
	# register to receive script or dynamic interface events
	# for example registering for "doMything" will give you a callback
	# if someone in the script calls "doMyThing()" the commandName parameter will be
	# "doMyThing" and will pass the positional
	# params, if any, as the positionalParms argument. 
	# if called from the action name of a dynamic interface element then the 
	# positionalParms will be empty and the dataParms will contain the current values
	# of all the elements in that dynamic interface and the key pointing to the 
	# control key that initiated the call. Callback format is:
	# myCallback( commandName, positionalParms, dataParms)
	#
	def addScriptHandler( self, scriptName, theCallback):
		
		if not scriptName in self._scriptHandlers:
			self._scriptHandlers[ scriptName] = [theCallback]
		else:
			self._scriptHandlers[ scriptName].append( theCallback)
	
	#
	#	REMOVE SCRIPT HANDLER
	#
	def removeScriptHandler( self, scriptName, theCallback):
		if scriptName in self._scriptHandlers:
			self._commandHandlers[ scriptName].remove[ theCallback]

	#
	#	HANDLE COMMAND FROM XTENSION
	#
	#	called by the XTension class received command handler when the target of the command
	# 	is a unit. If we have a handler registered for this command code then this executes it
	#
	def handleCommandFromXTension( self, theCommand):
	
		commandCode = theCommand.get( xtKeyCommand)
		
		#if XTension.debugMode:
		#	self.writeLog( '%s: handling command from XTension:' % self.name)
		#	theCommand.debugLog()
		
		if commandCode in self._commandHandlers:
			#self.debugLog( "a command handler was found")
			
			handlerList = self._commandHandlers[ commandCode]
			for handler in handlerList:
				# make sure that the handling continues even if the plugin code being called
				# causes an error, there may be others that can function properly in the list
				try:
					handler( theCommand)
				except Exception as e:
					self.writeLog( "XTUnit.handleCommandFromXTension( command=%s, error=%s)" % (commandCode, str( e)), xtLogRed)
					self.writeLog( traceback.format_exc(), xtLogRed)
		#else:
		#	self.debugLog( "command code (" + commandCode + ") was not handled in unit " + self.data.get( xtUnitKeyName))
 
# 			if XTension.debugMode:
# 				print( self._commandHandlers)
			
	
	
		
	#
	#    M E R G E   F R O M   D A T A 
	#
	# whenever a change is made to any unit settings or values the new information will show up here
	# only the changed values will be included so we must merge them with the existing values in our
	# xtData object. You can subscribe to any key values that you need to in order to see when something changed
	#
	def mergeFromData( self, theData):
		self.data.merge( theData)
	
	#
	# 	_ R U N   S C R I P T   C O M M A N D
	#
	# called when a doScript command is received from XTension and passes it off to any registered 
	# callbacks for it.
	#
	def _runScriptCommand( self, commandName, positionalParms, dataParms):
		if commandName in self._scriptHandlers:
			handlerList = self._scriptHandlers[ commandName]
			
			for handler in handlerList:		
				handler( commandName, positionalParms, dataParms)
		else:
			self.debugLog( "there was no handler for script call (%s)" % commandName)
			
		# also try to run it as just a local handler with the commandName and see if anything happens

	
	#
	#	G E T   &   S E T   &   E X I S T S
	#
	# just pass through to the .data object but I keep forgetting to type that so 
	# built these to pass the requests through
	#
	
	def get( self, key, default=None):
		return self.data.get( key, default)
		
	# note that this does not actually send the data to XTension
	def set( self, key, value):
		self.data.set( key, value)
		
	def exists( self, key):
		return self.data.exists( key)



#
#
#	X T   L I S T
#
#	the object representing a shared list of units
#
class XTList( XTSharedObject):
	pass






#
#	X T S C R I P T
#
#
# class representing a shared script in XTension
#



class XTScript( XTSharedObject):
	def __init__( self, theData):
		if isPy3:
			super().__init__( theData)
		else:
			XTSharedObject.__init__( self, theData)
		
		XTension.scriptIndexById[ self.uniqueId] = self
		XTension.scriptIndexByName[ self.name] = self
		
		# subscribe to the name in the data so that if the name is changed that we can change our index
		
		self.data.subscribe( [xtUnitKeyName], self.nameChanged, None)
		self.addCommandHandler( xtCommandUnitDeleted, self._scriptRemoved) #always run this internal handler
		
	def _scriptRemoved( self, theCommand):
		if self.uniqueId in XTension.scriptIndexById:
			del XTension.scriptIndexById[ self.uniqueId]
		
		if self.name in XTension.scriptIndexByName:
			del XTension.scriptIndexByName[ self.name]
			
		self.scriptRemoved()
		
	def scriptRemoved( self):
		# subclass me to handle actions when this script is no longer being shared
		pass
	
		
		
	# if the name changes in XTension then we need to update ourselves in the index
	def nameChanged( self, theKey, theValue, theTag, theData):
		if self.name in XTension.scriptIndexByName:
			del XTension.scriptIndexByName[ self.name]
			self.name = theValue
			XTension.scriptIndexByName[ self.name] = self
	
	#
	# executes the script in XTension
	#
	# all such commands must include the unique id of the script object
	# there is no support for executing a command by name
	#
	def execute( self):
		XTension.sendCommand( XTCommand(
			xtKeyCommandTarget 	= xtTargetGlobalScript,
			xtKeyUniqueId		= self.uniqueId,
			xtKeyCommand		= xtCommandExecuteGlobalScript))
				
	#
	# executes a handler in this global script named handlerName
	# if you wish to pass positional parameters to the handler
	# then include a list of strings in the paramDataList
	# only strings are supported but the script can
	def executeHandler( self, handlerName, paramDataList = []):
		
		XTension.sendCommand( XTCommand(
			xtKeyUniqueId 	= self.uniqueId,
			xtKeyCommand	= xtCommandScriptHandler,
			xtKeyCommandTarget 	= xtTargetGlobalScript,
			xtKeyName			= handlerName,
			xtKeyData			= XTension.encodeCommaSeparated( paramDataList)))
				
	#
	#	S E T   X T E N S I O N   D A T A
	#
	#	see XTUnit.setXTensionData for more info
	#
	def setXTensionData( self, key, value):
		x = XTCommand()
		x.set( xtKeyUniqueId, self.uniqueId)
		x.set( xtKeyCommand, xtCommandSetXMLData)
		x.set( xtKeyCommandTarget, xtTargetGlobalScript)
		x.set( xtKeyName, key)
		x.set( xtKeyValue, value)
		XTension.sendCommand( x)

	
class xtScript( XTScript):
	def __init__( self, theData):
		XTScript.__init__( self, theData)
		


						
	
#
#	X T U N I T
#
#
# subclass me for more unit functionality
# make sure to pass theData to the super constructor!
#

class XTUnit( XTSharedObject):

	def __init__(self, theData):
		
		if isPy3:
			super().__init__( theData)
		else:		
			XTSharedObject.__init__( self, theData)
		
		
		# verify that theData actually contains both a tag and an address before we can index it
		# no, thats OK, without that we just can't index by address and thats OK
		
		doAddressIndex = True
		
		if not theData.exists( xtUnitKeyTag):
			doAddressIndex = False
			self.tag = None
		else:
			self.tag = theData.get( xtUnitKeyTag)

		if not theData.exists( xtUnitKeyAddress):
			doAddressIndex = False
			self.address = None
		else:
			self.address = theData.get( xtUnitKeyAddress).upper()

			
		if doAddressIndex:
			XTension.unitIndexByAddress[ self.tag + self.address] = self
		
		XTension.unitIndexByName[ self.name] = self
		XTension.unitIndexById[ theData.get( xtUnitKeyUniqueId)] = self
		
		self.addCommandHandler( xtCommandUnitDeleted, self._unitRemoved) #always run this internal handler
		
		# if any of these values change we need to update our indexes for this unit
		self.data.subscribe( [xtUnitKeyName, xtUnitKeyAddress, xtKeyTag], self._indexChanged, None)
		
		
	# we have been removed either by deletion or by assigning to a different interface in XTension
	# this method must be called to manage the indexes you can subsclass the non underscore version
	
	def _unitRemoved( self, theCommand):	
		
		addressPath = self.data.get( xtUnitKeyTag, "notag") + self.data.get( xtUnitKeyAddress, "noaddress")	
		if addressPath in XTension.unitIndexByAddress:
			del XTension.unitIndexByAddress[ addressPath]
		
		myName = self.data.get( xtUnitKeyName)
		if myName in XTension.unitIndexByName:
			del XTension.unitIndexByName[ myName]
			
		myId = self.data.get( xtUnitKeyUniqueId)
		if myId in XTension.unitIndexById:
			del XTension.unitIndexById[ myId]
		
		self.unitRemoved()
			
		
		
		# called if the unit name, address or Tag is changed by editing in XTension
		# these are the values that we index ourselves by so it may be necessary to fix 
		# the indexes.
		# since the event is called before the data is updated we can look at the old values
		# and remove them from the index before re-adding the new one.
	def _indexChanged( self, theKey, theValue, theTag, theData):
	
		#maintain the local class variables that hold these things too
	
		if theKey == xtUnitKeyName:
			
			oldName = theData.get( xtUnitKeyName)
			
			if oldName in XTension.unitIndexByName:
				del XTension.unitIndexByName[ oldName]
							
			self.name = theValue
				
			XTension.unitIndexByName[ theValue] = self

			
			if XTension.debugMode:
				XTension.writeLog( "changing name in index from (" + oldName + ") to (" + theValue + ")")
			
			
		elif theKey == xtUnitKeyAddress:
			# addresses are a path consisting of the tag and the address
			# so we have to handle a potential change to both
			try:
				oldAddress = theData.get( xtUnitKeyTag, '') + theData.get( xtUnitKeyAddress, '')
				if oldAddress in XTension.unitIndexByAddress:
					del XTension.unitIndexByAddress[ oldAddress]
							
				self.address = theValue
				
				XTension.unitIndexByAddress[ theData.get( xtUnitKeyTag, '') + self.address] = self
				
			except Exception as e:
				XTension.debugLog( "error changing address " + str( e))
				XTension.writeLog( traceback.format_exc(), xtLogRed)
			
		
				
		elif theKey == xtUnitKeyTag:
						
			oldAddress = theValue + theData.get( xtUnitKeyAddress)
			
			if oldAddress in XTension.unitIndexByAddress:
				del XTension.unitIndexByAddress[ oldAddress]
				
			
			self.tag = theValue
				
			XTension.unitIndexByAddress[ theValue + theData.get( xtUnitKeyAddress)] = self
			
	
	#	U N I T   R E M O V E D
	# subclass this to manage your own structures when the unit is either deleted, no longer ours
	# or no longer being shared to us.
	def unitRemoved( self):
		pass
	

	#
	# S E N D   C O M M A N D
	#
	# use to send any command rather than the specific ones below if you need more
	# functionality in it. You can include any number of params to the command that will be
	# passed through into the command
	#
	#	this sets up the needed addressing by unique ID so that you do not have to include that
	#	in the code every time. This command will get sent to this unit.
	#
	#	use this like:
	#		theDict = {xtKeyCommand:xtCommandOn}
	#		self.sendCommand( **theDict)
	#
	
	def sendCommand( self,  **kwds):
	
		kwds[ xtKeyUniqueId] = self.uniqueId
		kwds[ xtKeyCommandTarget] = xtTargetUnit
		
		XTension.sendCommand( XTCommand( **kwds))
# 	
# 		kwds.update( {
# 			xtKeyUniqueId:self.uniqueId, 
# 			xtKeyCommandTarget:xtTargetUnit})
# 			
# 		XTension.sendCommand( XTCommand( **kwds))
		
		# 
# 		x = XTCommand( **kwds)
#  		x.set( xtKeyUniqueId, self.uniqueId)
#  		x.set( xtKeyCommandTarget, xtTargetUnit)
# 		
# 		XTension.sendCommand( x)
# 		
	#
	#	S E T   B A T T E R Y   L E V E L
	#
	#	will only send the command if the battery level is different
	# 	than our current one. Uses a separate command to set it rather than including it
	# 	in a regular command as you would want to do if you needed another command handled
	#	at the same time
	#
	def setBatteryLevel( self, newLevel):
		if int( newLevel) != int( self.data.get( xtUnitKeyBatteryLevel, -1)):
			self.sendCommand( 
				xtKeyCommand = xtCommandNoOp, 
				xtKeyBatteryLevel=newLevel)
	
	#
	#  T U R N   O N
	#
	#
	# use named parms to send extra data other than the defaultLabel and updateOnly
	#
	# thisUnit.turnOn( xtKeyColor="FF4455") or something like that to include that in the
	# outgoing command.
	
	def turnOn( self, updateOnly = False, defaultLabel = None, **kwds):
		# by passing the kwargs we are allowed to do the above mentioned xtKeyColor= stuff
		
		kwds[ xtKeyCommand] = xtCommandOn
		if updateOnly:
			kwds[ xtKeyUpdateOnly] = xtTrue
			
		if defaultLabel != None:
			kwds[ xtKeyDefaultLabel] = defaultLabel
			
		self.sendCommand( **kwds)
# 		
# 		
# 		x = XTCommand( **kwds)
# 		x.set( xtKeyUniqueId, self.uniqueId)
# 		x.set( xtKeyCommand, xtCommandOn)
# 
# 		if updateOnly:
# 			x.set( xtKeyUpdateOnly, xtTrue)
# 		
# 		if defaultLabel != None:
# 			x.set( xtKeyDefaultLabel, defaultLabel)
# 			
# 		XTension.sendCommand( x)
		
	#
	#  T U R N   O F F
	#
		
	def turnOff( self, updateOnly = False, defaultLabel = None, **kwds):
		# by passing the kwargs we are allowed to do the above mentioned xtKeycolor stuff
		# though you can't pass a color with an OFF command, it will be ignored.
		
		kwds[ xtKeyCommand] = xtCommandOff

		if updateOnly:
			kwds[ xtKeyUpdateOnly] = xtTrue
		
		if defaultLabel != None:
			kwds[ xtKeyDefaultLabel] = defaultLabel
			
		self.sendCommand( **kwds)



	#
	#	T O G G L E
	#
	def toggle( self, updateOnly = False, defaultLabel = None, **kwds):
		if updateOnly:
			kwds[ xtKeyUpdateOnly] = xtTrue
		
		if defaultLabel != None:
			kwds[ xtKeyDefaultLabel] = defaultLabel
		
		if self.getState():
			kwds[ xtKeyCommand] = xtCommandOff
		else:
			kwds[ xtKeyCommand] = xtCommandOn
			
		self.sendCommand( **kwds)


	
	#
	#  S E T   V A L U E
	# newValue can be anything that can be passed through str() to get a string of the number
	# continue to support the old stacked parameters for updateOnly and defaultLabel but in the
	# future please use only the kwds so pass more readable strings like xtKeyUpdateOnly = True etc.
	#
	
	def setValue( self, newValue, updateOnly = False, defaultLabel = None, **kwds):
		# by passing the kwargs we can do things like the above mentioned xtKeyColor=
		
		kwds[ xtKeyCommand] = xtCommandSetValue
		kwds[ xtKeyValue] = newValue
		
		if updateOnly:
			kwds[ xtKeyUpdateOnly] = xtTrue
		
		if defaultLabel != None:
			kwds[ xtKeyDefaultLabel] = defaultLabel
			
		self.sendCommand( **kwds)
# 		
# 		
# 		x = XTCommand( **kwds)
# 		x.set( xtKeyUniqueId, self.uniqueId)
# 		x.set( xtKeyCommand, xtCommandSetValue)
# 		x.set( xtKeyValue, newValue)
# 
# 		if updateOnly:
# 			x.set( xtKeyUpdateOnly, xtTrue)
# 		
# 		if defaultLabel != None:
# 			x.set( xtKeyDefaultLabel, defaultLabel)
# 
# 		XTension.sendCommand( x)
		
	
	#
	#	S E N D   N O O P
	#
	#	can be used to include a battery or error message without performing an action
	#	will also update the last message received (but not the last activity date) for a unit
	#	in order to know that it is active or valid or operating properly. That time can 
	#	be used in XTension to know if a unit say holding a temp value or something is
	#	sill receiving updates. Mostly another error should be set specifically but there
	#	may be cases where this is useful as well.
	#
	
	def sendNoOp( self, **kwds):
	
		kwds[ xtKeyCommand] = xtCommandNoOp
		self.sendCommand( **kwds)
# 		
# 		x = XTCommand( **kwds)
# 		x.set( xtKeyUniqueId, self.uniqueId)
# 		x.set( xtKeyCommandTarget, xtTargetUnit)
# 		
# 		x.set( xtKeyCommand, xtCommandNoOp)
# 		XTension.sendCommand( x)
		

	
	
	#
	#	S E T   P R E S E T
	#
	#	sets the preset level in XTension, this is the value that will be included with the next
	#	turnon command that your device should return to when next turned on locally or via remote
	#
	def setPreset( self, newValue):
		self.setXTensionData( xtUnitKeyPresetLevel, newValue)
		

	#
	#	S E T   D E S C R I P T I O N
	# TODO: check this against the current value and only send the command if different
	def setDescription( self, newValue, **kwargs):
	
		kwargs[ xtKeyCommand] = xtCommandSetDescription
		kwargs[ xtKeyData] = newValue
		
		self.sendCommand( **kwargs)
		
	#
	#	G E T   D E S C R I P T I O N
	#
	def getDescription( self):
		return self.data.get( xtUnitKeyDescription, '')


	#
	#	G E T   B L O C K E D
	#
	def getBlocked( self):
		#self.writeLog( "    in getBlocked value=(%s) type=(%s)" % (self.data.get( xtUnitKeyBlocked, "(none)"), type( self.data.get( xtUnitKeyBlocked, "(none"))))	
		#return self.data.get( xtUnitKeyBlocked, xtFalse)
		
		# so it turns out this returns a string as well
		# but someday I might fix that so prepare for it to be a proper boolean here
		amBlocked = self.data.get( xtUnitKeyBlocked, False)
		
		if type( amBlocked) == bool:
			return amBlocked
		
		return amBlocked == xtTrue
		
	
	#
	#	S E T   X T E N S I O N   D A T A
	#
	# sets or changes a keyed value in the root of the Units data
	# similar to the XTension classes .setData() method
	# this is the data that is used by your dynamic interfaces
	# and all the build in unit settings so be sure to verify
	# your name space. This is the data that will end up in the
	# self.data xtData object of the unit. The self.data object 
	# will be updated automatically sometime after you issue this
	# command. It is not necessary to set it in both places.
	#
	
	def setXTensionData( self, key, value, **kwargs):
	
		# set the value locally here so it will be immediately available
		# no longer necessary to do this as a separate step
		self.data.set( key, value)
	
		kwargs[ xtKeyCommand] = xtCommandSetXMLData
		kwargs[ xtKeyName] = key
		kwargs[ xtKeyValue] = value
		
		self.sendCommand( **kwargs)
	
	
	#
	#	S E T   D E F A U L T   L A B E L
	#
	# sends a textual string to display in all value displays for the unit instead of the
	# numerical or standard state display. This is usually included as a key in some other
	# command but this method can be used to send it as a separate NoOp command if needed
	# note that the user can still override this and display whatever they wish including
	# the raw value if they set the standard on/off labels for the unit in XTension
	# this will only be displayed if you have not set the on/off labels when creating the
	# unit.
	#
	def setDefaultLabel( self, newLabel, **kwargs):
	
		kwargs[ xtKeyCommand] = xtCommandNoOp
		kwargs[ xtKeyDefaultLabel] = newLabel
		self.sendCommand( **kwargs)
		
	def getDefaultLabel( self):
		return self.data.get( xtUnitKeyDefaultLabel, "(none)")
		
	#
	#	R E M O V E   X T E N S I O N   D A T A 
	#
	# deletes a keyed entry in the unit or interface
	# verify namespace and use only on your own properties
	# or unexpected and less than useful results will result
	# do not try to remove or edit built in XTension unit properties
	#
	
	def removeXTensionData( self, key):
	
		self.sendCommand(
			xtKeyCommand 	= xtCommandRemoveXMLData,
			xtKeyName 		= key)
# 	
# 		XTension.sendCommand( XTCommand(
# 				xtKeyUniqueId 		= self.uniqueId,
# 				xtKeyCommandTarget	= xtTargetUnit,
# 				xtKeyCommand		= xtCommandRemoveXMLData,
# 				xtKeyName			= key))
		
	
	#
	#	S E T   P R O P E R T Y
	#
	# shortcut to set a unit property
	# can accept any value that can be coerced to a string
	# same as the applescript setUnitProperty command
	#
	# updated to also accept kwargs to add extra stuff
	#
	def setProperty( self, key, value, **kwargs):
	
	
		kwargs[ xtKeyCommand] 	= xtCommandSetUnitProperty
		kwargs[ xtKeyName]		= key
		kwargs[ xtKeyData]		= value
		
		self.sendCommand( **kwargs)
		
	
# 		self.sendCommand(
# 			xtKeyCommand 	= xtCommandSetUnitProperty,
# 			xtKeyName 		= key,
# 			xtKeyData 		= value)
	

	#
	#	G E T   P R O P E R T I E S
	#
	# returns an xtData object that represents the Unit Properties
	# for this unit. Use the above command "setProperty" to set a property
	# as these are kept updated by XTension but changes made locally to them are not
	# sent upstream to XTenstion. These should be considered as read only but they will
	# change as updates are received from XTension.
	#
	
	def getProperties( self):
		return( self.data.getContainer( xtUnitKeyProperties, 1))
		

	#
	#	G E T   C O L O R   A S   H T M L
	#
	#	internal color format in XTension database is RGB as decimal separated by commas
	#	this returns a standard HTML color string but without the preceding "#"
	#
	def getColorAsHTML( self):
		workColor = self.data.get( xtUnitKeyColor, None)
		if workColor == None:
			return None
			
		return "{:02x}{:02x}{:02x}".format( int( workColor[0]), int( workColor[1]), int( workColor[2]))

	#
	#	S E T   E R R O R
	#
	# called to set or clear a unit error
	# pass a 0 as the number to clear an error with an empty message
	# the two keys for error number and error message can also be included in any other
	# command going to the unit, but this will generate a separate NoOp command that
	# only includes this information
	# compares the new values with the current values and no update is sent if they are the same
	# so it's not necessary to check for that every time in your own code
	#
	
	def setError( self, errorNum, errorMessage, **kwargs):

		# if sent the same error number then just send nothing
		if int( self.data.get( xtUnitKeyErrorLevel, 0)) == int( errorNum):
			return

		kwargs[ xtKeyCommand] 		= xtCommandNoOp
		kwargs[ xtKeyCommError]		= errorNum
		kwargs[ xtKeyErrorMessage] 	= errorMessage

		self.sendCommand( **kwargs)


		
	#
	#	W R I T E   L O G
	#
	# used to send a log with the properties of the unit in it rather than just a global log
	# this way you can filter on the unit in XTension and see just log lines that came from
	# this unit. 
	#
	
	def writeLog( self, msg, color="2"):
		
		self.sendCommand(
			xtKeyCommand 		= xtCommandWriteLog,
			xtKeyValue 			= color,
			xtKeyData 			= msg)
# 		
# 		XTension.sendCommand( XTCommand(
# 			xtKeyCommand		= xtCommandWriteLog,
# 			xtKeyValue			= color,
# 			xtKeyData			= msg,
# 			xtKeyUniqueId		= self.uniqueId,
# 			xtKeyCommandTarget	= xtTargetUnit))

	#
	#	W R I T E   D E B U G   L O G
	#
	# same as write log, but only goes through if we're in debug more
	#
	
	def debugLog( self, msg, color="2"):
		if XTension.debugMode:
			self.writeLog( msg, color)

	#
	#	G E T   S T A T U S
	#	G E T   S T A T E
	#
	# status really is different than state, but I have used them interchangeably so continue to allow that here
	#
	def getStatus( self):
		return (xtFloat(self.get( xtUnitKeyValue, 0.0)) != 0.0)
	
	def getState( self):
		return (xtFloat( self.get( xtUnitKeyValue, 0.0)) != 0.0)
		
	#
	#	G E T   V A L U E
	#
	
	def getValue( self):
		return xtFloat(self.get( xtUnitKeyValue, 0))
		
	#
	#	G E T   P R E S E T
	#
	#	return the preset level that we would return to with the next simple on command
	#
	def getPreset( self):
		return xtFloat( self.get( xtUnitKeyPresetLevel, 100))
		
	#
	#	S E T   P R E S E T
	#
	# set the preset level in XTension for this unit to the new value
	# compares against the current value to make sure it is not sending commands 
	# unnecessarily
	def setPreset( self, newPreset):
		if self.getPreset() == newPreset:
			return
		
		self.setXTensionData( xtUnitKeyPresetLevel, newPreset)
		
	#
	#	E X E C U T E   H A N D L E R
	#
	# runs a handler in the on script with the passed data
	#
	#	TODO abandon this stupid comma separated value list and instead switch to a
	#	JSON data string so that we can actually use typed values properly on both ends
	#
	
	def executeHandler( self, handlerName, paramDataList = []):
	
		self.sendCommand(
			xtKeyCommand 		= xtCommandScriptHandler,
			xtKeyName 			= handlerName,
			xtKeyData 			= XTension.encodeCommaSeparated( paramDataList))
# 		
# 		XTension.sendCommand( XTCommand( 
# 			xtKeyUniqueId = self.uniqueId,
# 			xtKeyCommand = xtCommandScriptHandler,
# 			xtKeyCommandTarget = xtTargetUnit,
# 			xtKeyName = handlerName,
# 			xtKeyData = XTension.encodeCommaSeparated( paramDataList)))


#
# this is a catcher subclass so I don't have to rebuild all the 
# classes I used in other plugins that I used the capitalization wrong
class xtUnit( XTUnit):
	def __init__( self, theData):
		if isPy3:
			super().__init__( theData)
		else:
			XTUnit.__init__( self, theData)
		


#
#	x t D O L A T E R
#
# a thread that waits a certain number of seconds to do something and can be delayed
# by resetting the timeout. Good for sending a status update after a certain time or
# something similar. Repeated calls to setTimeout will just push back the time.
#
class XTDoLater:
	def __init__( self):
		self._timeLeft = -1 # -1 means our time has expired and we've already run our handler
		self._thread = None
		self.threadName = 'XTDoLater' # you can set this in your own subclassed init method if you like
		
		
	def setTimeout( self, newTimeout):
		self._timeLeft = newTimeout
		# if the thread already exists then it's already counting down
		if self._thread == None:
			self._thread = Thread( target=self._threadedTimer, args=(), name=self.threadName)
			self._thread.start()
		
		
	def _threadedTimer( self):
		while self._timeLeft > -1 and not XTension.isShuttingDown:

			sleep( 1)

			self._timeLeft -=1 
			
		self.action()
		self._thread = None
		
			
		
		
	#
	#	A C T I O N
	#
	# subclass to add custom code to this method
	#
	def action( self):
		XTension.writeLog( "subclass the action method to add your own event")
		
	

		
		
		

#
#	x t T I M E R
#
#	THIS IS DEPRECATED do not use this class in new plugins it is not reliable
#	please just use a regular thread and sleep on it, or use the XTDoLater class above
#
# used to create a repeating callback to it's subclassed action() handler
# subclass this class and add your own action( self) handler that will be called
# when the period expires.
#
# use the start() and stop() handlers to start and stop the timer. Note that just letting
# the class go out of scope will not stop the timer.
# if you wish to be able to stop the timer you must keep a reference to the timer so you 
# can call stop, or have some mechanism to call stop from the action event.
#
# any timer that tries to fire once the XTension class is shutting down will be cancelled
#
# You can't create any timers until after the connection to XTension is established
# as the callback relies on the global XTension to be set and pointing to the cXTension object
#
#	the inPeriod for the constructor and the setPeriod is in seconds
#		


class XTTimer:
	def __init__( self, inPeriod):
		self.isRunning = False
		self.period = inPeriod
		self.thread = None
	
		
	#
	# 	A C T I O N
	#	
	# subclass this class and add your own action handler
	# it will be called regularly every interval that is set
	# until you call the stop() action on the class
	# note that just letting the class go out of scope will not
	# stop the timer, you must call stop() to stop the timer first
	# keep a reference to the subclass so that you can stop it.
	# 	
	#
	
	def action( self):
		print( "subclass me to make event")
		

	#
	# 	S T A R T
	# 
	# called to start the timer
	# the period must have already been passed to the constructor
	# or changed by a call to setPeriod
	# calling start multiple times is equivalent to calling 
	# setPeriod with the same interval it cancels any currently outstanding
	# timer and resets it to the current period. So calling start will reset the timer
	# good for timeouts and such.
	#
	
	def start( self):
		if self.thread != None:
			# just in case a timer thread is already waiting go ahead and cancel it
			self.thread.cancel()
			
		# subscribe to the XTension shutdown command so that we will be stopped and ready to quit properly
		XTension.addCommandHandler( xtCommandShutdown, self.xtensionShutdown)

			
		self.isRunning = True
		self.thread = Timer( self.period, self._action)
		self.thread.start()
		
	#
	# 	S T O P
	#
	# stops any currently outstanding timer threads and sets isRunning to false
	# so that if called from inside the action event no new thread will be created
	#
	
	def stop( self):
		self.isRunning = False
		
		if self.thread != None:
			self.thread.cancel()
			self.thread = None
			
		XTension.removeCommandHandler( self.xtensionShutdown, None)

	#
	# 	S E T   P E R I O D
	#
	# changes the period of an already created timer
	# works if the timer is currently running or currently stopped
	# changing the period or just setting it to the same value resets the
	# timer and the new period begins counting from then if the timer is running
	# if the timer is stopped then nothing happens, you must call start again
	#
	def setPeriod( self, newPeriod):
	
		# is running cannot be true if there is no self.thread so
		# there is no need to check against none
		if self.isRunning:
			self.thread.cancel()
			
		self.period = newPeriod
		
		# if we were running then restart us
		if self.isRunning:
			self.start()
	
		
	#
	# internal action handler, this is the actual callback from the Timer thread
	# this handles making sure that you should actually be firing, executes your
	# subclassed action handler and then if you haven't called stop() in the action
	# then creates the next timer thread.
	#
		
	def _action( self):
		#internal action handler that restarts the timer
	
		if not self.isRunning:
			#if XTension.debugMode:
			XTension.writeLog( "xtTimer.action after having stopped", xtLogRed)
				
			# we should not be firing we should just return
			return
	
		if not XTension.isShuttingDown:
		
			# so that an error in the subclassed action handler won't result in 
			# the entire thing falling out here and stopping we will handle any
			# otherwise unhandled errors and log them so we can keep going
			try:
				self.action()
			except:
				(theType, theValue, theTraceback) = sys.exc_info()
				XTension.writeLog( "Error in xtTimer.action: type=%s value=%s" % (theType, theValue))
				#XTension.writeLog( "Error in xtTimer.action: type=" + str( theType) + " value=" + str( theValue), xtLogRed)
				theType = None
				theValue = None
				theTraceback = None
				XTension.writeLog( traceback.format_exc(), xtLogRed)
		
			# if you called to stop() inside the action event then
			# isrunning will have become false here
			# if isRunning is still True then we must create a new
			# Timer thread and start it up

			if self.isRunning:
				self.thread = Timer( self.period, self._action)
				self.thread.start()
		else:
			self.isRunning = False
	
	#
	# 	X T E N S I O N   S H U T D O W N
	#
	# subscribed to the shutdown command so that we can stop any outstanding threads
	# here and not keep the plugin from quitting, or have to force it to wait for the 
	# action to run so that it will find that XTension is shutting down
	#
	def xtensionShutdown( self, theCommand):
		self.stop()
		
# and just this because I was sloppy in my naming conventions at the beginning and some
# of the original plugins built with this may call it xtTimer instead of XTTimer
class xtTimer( XTTimer):
	def __init__( self, inPeriod):
		XTTimer.__init__( self, inPeriod)

	
			
		
			
			
				
		
#
#	class 	X T   R E M O T E   C O N N E C T I O N
#
# I find myself having to re-create a lot of this code for each plugin and so I've decided
# to make it part of the plugin helper files so that it can be re-used. 
# this class can be used to make either an outgoing TCP connection or a Serial Port connection
# based on the users setup in XTension. You should subclass it for your use. The events that
# will be called that you should subclass are the "connected" "dataAvailable" and "error" 
# handlers.
#
# use the self.buffer to get the data currently in the buffer. The dataAvailable event does not
# pass you data from that event, but the newly received data is appended to the buffer before
# that event is called.
#
# by default this will use the default settings from XTension
# if you need to override that and connect on a different port or via UDP or something else
# then use the kwds to send specific keys overriding the xtension.settings object
# and if you need to listen or send to UDP then you need to send those keys too as there
# is no (wow premature end of comment...)

class XTRemoteConnection:

	def __init__( self, **kwds):
		self.sock = None
		self.closed = False
		self.errorSent = False # keeps from logging errors constantly
		self.buffer = b''
		self.isConnected = False # deprecated, use connected
		self.connected = False
		self.workThread = None
		self.writeLock = threading.Lock() # control threaded access to the outgoing socket
		self.overrideParms = kwds
		self.remoteAddress = "" # used when receiving a UDP packet so you can see who it's from
		self.listenType = xtKeyListenTypeTCP
			# the remote address of an incoming TCP connection is available in your subclass of that thread
			# a subclass is not necessary for the UDP server as it's not a stream and so is not threaded.
		self.lastRead = b''
		
		self.connectedThreads = [] # an array to hold a reference to the connected threads so that they don't get removed before we're done with them

		
		self.connectionMethod = xtPortNameNone
		
		
		# create the proper connection method based on the users preferences
		# TODO: also support incoming connections
		# TODO: add thread protection with locks in the write methods
		

		portName = self.getParm( xtKeyPortName, None)
		
		if portName == None or portName == xtPortNameNone:
			# this is not necessarily an error some plugins may run OK with no port selected
			# though I dont know why you'd be instantiating this class then
			XTension.debugLog( "no port specified")
			return
		elif portName == xtPortNameOutgoingTCP:
			XTension.debugLog( "opening outgoing TCP connection")
			self.connectionMethod = xtPortNameOutgoingTCP
			
			self.workThread = Thread( target=self.TCPSocketThread, args=())
			self.workThread.start()
			
		elif portName == xtPortNameListen:

			self.listenType = self.getParm( xtKeyListenType, xtKeyListenTypeTCP)
			self.connectionMethod = xtPortNameListen
			
			if self.listenType == xtKeyListenTypeTCP:		
				XTension.debugLog( "starting TCP listening server")
				
				self.workThread = Thread( target=self.TCPServerThread, args=())
				self.workThread.start()
				
			elif self.listenType == xtKeyListTypeUDP:
				XTension.debugLog( "starting UDP listening server")
				
				self.workThread = Thread( target=self.UDPServerThread, args=())
				self.workThread.start()
				
			else:
				XTension.debugLog( "unknkown listen type requested (%s)" % self.listenType)
			
		
		else:
			self.connectionMethod = 'serial'
			
			XTension.debugLog( "opening serial port connection to port: " + portName)
			# so... I never implemented the serial connection here? I definitely meant to do that...
			# well I guess I'll do that now so I don't have to keep doing it later
			
			self.workThread = Thread( target=self.serialThread, args=())
			self.workThread.start()
			
			
	#
	#	CLOSE
	#
	# closes the connection or stops the server or whatever
	#
	
	def close( self):
		self.isConnected = False
		self.buffer = b''
		self.connected = False
		self.closed = True # this keeps it from reconnecting upon the closed error
		
		
		if self.sock != None:
			try:
				self.sock.shutdown( socket.SHUT_RDWR)
				self.sock.close()
				self.sock = None
			except Exception as e:
				pass
		
		if self.serialPort != None:
			try:
				self.serialPort.close()
				self.serialPort = NOne
			except:
				pass
	
	
	#
	#	SERIAL THREAD
	#
	#	the thread started if this is a request to make a serial connection
	#
	def serialThread( self):
	
		self.serialPort = None
		errorSent = False # dont log constantly, just when we have an error
		self.closed = False
		
		# need this outside of the loop so we can log errors properly
		portPath = '/dev/tty.notset'
	
		# if XTension is shutting down we should stop restarting the connection
		# also if we have specifically had our close call above called then we should
		# also close and release the port


		while not XTension.isShuttingDown and not self.closed:
			# if we dont have a port, or if we lost it due to error then try to create it again
			if self.serialPort == None:
				try:
					portPath = '/dev/tty.' + XTension.settings.get( xtKeyPortName, 'none')


					XTension.writeLog( "baud: %s bits: %s parity: %s stopBits: %s" % (self.getParm( xtKeyBaud, 9600), self.getByteSize(), self.getParity(), self.getStopBits()))
					
					self.serialPort = serial.Serial( 
						port 			= portPath,
						baudrate 		= self.getParm( xtKeyBaud, 9600),
						bytesize 		= self.getByteSize(),
						parity 			= self.getParity(),
						stopbits 		= self.getStopBits(),
						timeout 		= 1,	# we want the timeout so it can drive timers and be the same as the socket implementation
						xonxoff 		= self.getParm( xtKeyHandshakeXONXOFF, False),
						rtscts 			= self.getParm( xtKeyHandshakeRTSCTS, False),
						dsrdtr 			= self.getParm( xtKeyHandshakeDSRDTR, False))

					# if requested turn on the rts and or dtr pins
					# note that this will be either ignored or break things or behave strangely
					# if any hardware flow control is turned on as well.
					self.serialPort.rts = self.getParm( xtKeyRTSOn, False)
					self.serialPort.dtr = self.getParm( xtKeyDTROn, False)
					
					# flush the buffer. Not sure this will actually do anything in this case if the 
					# interface itself is doing the buffering and not the system level part of it
					# but still anything to avoid a bolus of stale data at connection should be attempted
					self.serialPort.reset_input_buffer()
					

					XTension.setRunState( xtRunStateOK, "Port Opened: %s" % portPath)
					errorSent = False
					self.connected = True
					
					try:
						self.eventConnected()
					except Exception as e:
						XTension.writeLog( "Error in serial port connected event: %s" % e, xtLogRed)
						
					
					
				except Exception as e:
					self.serialPort = None

					XTension.setRunState( xtRunStateError, "error opening port: %s" % portPath)
					if not errorSent:
						errorSent = True
						XTension.writeLog( "Unable to open serial port: %s  %s" % (portPath, e))
						
					try:
						# return true from the handler to make this not log it's own error
						if not self.error( e):
							XTension.writeLog( "Error opening port: %s" % e, xtLogRed)
							XTension.writeLog( traceback.format_exc(), xtLogRed)
							
					except Exception as e:
						XTension.writeLog( "error in error handler itself: XTRemoteConnection.serialThread.error( %s)" % e, xtLogRed)
						XTension.writeLog( traceback.format_exc(), xtLogRed)
					
					# sleep and try again in case the port shows up or is able to be opened later
					sleep( 1)
					continue
					
				
				
				
			# if we get here then we should have a valid serial port object
			try:
				# block until we get a single character
				# then read as many as are available, then call the dataAvailable event
				# the read will be empty if there was a timeout it seems
				self.lastRead = self.serialPort.read( 1)

				if self.lastRead == b'':
					# normal timeout? should just loop and check again for if we are closed on purpose
					# or XTension is shutting down
					
					# also call through to the socketTimeout subclassed handler for local timers and such
					
					try:
						self.socketTimeout()
					except Exception as e:
						XTension.writeLog( "Error in xtRemoteConnection.socketTimeout( %s)" % e, xtLogRed)
					
					continue
				
				#self.buffer += firstChar
				available = self.serialPort.in_waiting
				while available > 0:
					self.lastRead += self.serialPort.read( available)
					available = self.serialPort.in_waiting
					
				#print( "read( %s)" % self.lastRead)
				
				self.buffer += self.lastRead
				
# 				if available > 0:
# 					#self.buffer += self.serialPort.read( available)
# 					nextBlock = self.serialPort.read( available)


# 				print( "about to call data available")
				self.dataAvailable()
				continue
					
				
			except Exception as e:
				XTension.debugLog( "exception in Serial Read Thread: %s" % e)

				if XTension.isShuttingDown:
					sys.exit()
					return
				try:
					self.error( e)
				except Exception as f:
					XTension.writeLog( "Error in XTRemoteConnection.TCPSocketThread( %s) and a further error in XTRemoteConnection.error( %s)" % (e, f), xtLogRed)
					
				sleep( 2)
				continue
								


					
	
	def getByteSize( self):
		value = self.getParm( xtKeyBits, 8)

		if value == 5:
			return serial.FIVEBITS
		elif value == 6:
			return serial.SIXBITS
		elif value == 7:
			return serial.SEVENBITS
		else:
			return serial.EIGHTBITS

	def getParity( self):
		value = self.getParm( xtKeyParity, 'none')
		
		if value == xtKeyParityOdd:
			return serial.PARITY_ODD
		elif value == xtKeyParityEven:
			return serial.PARITY_EVEN
		elif value == xtKeyParityMark:
			return serial.PARITY_MARK
		elif value == xtKeyParitySpace:
			return serial.PARITY_SPACE
		else:
			return serial.PARITY_NONE


	def getStopBits( self):
		value = self.getParm( xtKeyStopBits, 1)
		
		if value == 2:
			return serial.STOPBITS_TWO
		else:
			return serial.STOPBITS_ONE






	
	#
	#	THREADED SOCKET
	# used to make an outgoing TCP connection and send events back to the subclass
	# single threaded outgoing TCP connection
			
		
	def TCPSocketThread( self):
	
		while not XTension.isShuttingDown and not self.closed:
			if self.sock == None:
				if not self.makeTCPConnection():
					# failed to start the connection, sleep for a couple of seconds and try again
					self.isConnected = False # DEPRECATED use .connected
					self.connected = False
					sleep( 2)
					continue
					
					
				self.isConnected = True # DEPRECATED use connected
				self.connected = True

			# read data and pass to subclassed event
			
			try:
				newData = self.sock.recv( 1024)
				
				# newData will be empty if the socket has closed sometimes without an 
				# error being caught so we need to treat this like an error
				
				if newData == '':
					if XTension.isShuttingDown:
						sys.exit()
						return
					
					self.isConnected = False # DEPRECATED use connected
					self.connected = False
					self.error( 'disconnected')
					
					XTension.debugLog( "attempting to restart connection after empty reception")
					
					sleep( 2)
					# setting this to none forces the check above to re-create the socket and retry
					self.sock = None
					continue
			
			except socket.timeout:
				# this is OK we just continue unless XTension is shutting down
				# but also pass through this event to the subclass if they have
				# implemented this as it's useful for doing pings and other things
				
				self.socketTimeout()
				
				continue
				
			except Exception as e:
				XTension.debugLog( "exception in TCPSocket Read")
				self.isConnected = False
				self.connected = False
				self.sock = None
				if XTension.isShuttingDown:
					sys.exit()
					return
				try:
					self.error( e)
				except Exception as f:
					XTension.writeLog( "Error in XTRemoteConnection.TCPSocketThread( %s) and a further error in XTRemoteConnection.error( %s)" % (e, f), xtLogRed)
					
				sleep( 2)
				continue
				
			
			#
			# append to the buffer 
			#
			self.buffer += newData
			
			#
			# call the dataAvailable event in the subclass so that they can process this
			#
			self.dataAvailable()
			
	#
	#	SOCKET TIMEOUT
	#
	# subclass to get an event every second as the socket times out
	# good for doing pings or keeping track of other things
	#
	# this does nothing in the super class
	#
	def socketTimeout( self):
		pass
			
	#
	#	TCPServerThread
	#
	# if creating a listening TCP server then this will be the thread that is used
	# subclass the 
	
	def TCPServerThread( self):
		
		TCP_KEEPALIVE = 0x10
		try:
			self.sock = socket.socket( socket.AF_INET, socket.SOCK_STREAM)
			self.sock.setsockopt( socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
			self.sock.setsockopt( socket.IPPROTO_TCP, TCP_KEEPALIVE, 60)
			# interestingly enough it seems that setting the TCP_KEEPALIVE here does nothing
			# as that is on the listening socket. It does not carry through to the received
			# sockets so add that to the ones we receive.
			
			# the addresss to bind to should be either what we get from getIp or 0.0.0.0
			# or whatever is set in XTension
			
			# TODO: add script handler to set the local address
			
			if XTension.settings.exists( xtKeyForceIp):
				listenNetwork = XTension.settings.get( xtKeyForceIp)
			else:
				listenNetwork = self.getParm( xtKeyLocalAddress, None)
				
				if listenNetwork == None or listenNetwork == '127.0.0.1':
					listenNetwork = getIp()
					
			listenPort = int( self.getParm( xtKeyRemotePort, -1))
			
			if listenPort == -1:
				XTension.writeLog( "no port was specified for the listening TCP server. Cannot startup", xtLogred)
				XTension.setRunState( xtRunStateFail, "no port specified")
				self.isConnected = False
				self.connected = False
				return
				
			# not sure this will work actually but want to be able to stop the listen if we 
			self.sock.settimeout( 1)
				
			self.sock.bind( (listenNetwork, listenPort))
			
			self.sock.listen( 10)
			self.connected = True
			self.listening()
			
		except Exception as e:
			self.isConnected = False
			self.connected = False
			self.error( e)
			XTension.setRunState( xtRunStateFail, str( e))
			sys.exit()
			return
			
			
		while not XTension.isShuttingDown:
			
			try:
				workSock, addr = self.sock.accept()
				
			except socket.timeout as e:
				# timeout just lets us check for being shut down
				continue
			
			except Exception as e:
			
				if XTension.isShuttingDown:
					sys.exit()
					return

				self.isConnected = False
				self.connected = False
				self.error( e)
				
			# startup the thread handler for the connection
			
			# attempt setting the socket keep alive here then rather than on the server itself
			#workSock.setsockopt( socket.IPPROTO_TCP, TCP_KEEPALIVE, 30)
			# AH but this is the incoming server stuff, and that is not what I was trying to fix arrg...
			
			
			workThread = self.makeTCPServerThread( addr[0])
			
			if workThread == None:
				XTension.debugLog( "connection from %s was refused" % addr[0], xtLogRed)
				try:
					workSocket.close()
				except:
					pass
					
				workSocket = None
				continue
			
			self.connectedThreads.append( workThread)
			
			#def _setup( self, ip, port, sock, myServer):

			workThread._setup( addr[0], addr[1], workSock, self)
					
	#
	#	MAKE TCP SERVER THREAD
	#
	# you must subclass this if you're making a TCP or UDP server as a thread needs to be created
	# to handle the connection or everything else will block. This should return your subclass of
	# XTTCPServerThread
	# if you return none from this then the connection will be refused instantly
	# so you can validate an IP address or something else at this point and refuse the connection
	#
	
	def makeTCPServerThread( self, remoteAddress):
		return XTTCPServerConnection()
			
			
			
	#
	# 	UDP Server Thread
	#
	# received UDP packets will show up in the dataAvailable method which you should 
	# overload in your subclass of XTRemoteConnection
	
	def UDPServerThread( self):

		try:
			self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
			self.sock.setsockopt( socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

			# the addresss to bind to should be either what we get from getIp or 0.0.0.0
			# or whatever is set in XTension
			
			# TODO: add script handler to set the local address
			
			if XTension.settings.exists( keyForceIp):
				listenNetwork = XTension.settings.get( keyForceIp)
			else:
				listenNetwork = self.getParm( xtKeyLocalAddress, None)
				
				if listenNetwork == None or listenNetwork == '127.0.0.1':
					listenNetwork = getIp()
					
			listenPort = int( self.getParm( xtKeyRemotePort, -1))
			
			if listenPort == -1:
				XTension.writeLog( "no port was specified for the listening UDP server. Cannot startup", xtLogred)
				XTension.setRunState( xtRunStateFail, "no port specified")
				self.isConnected = False
				self.connected = False
				return
				
			
			self.sock.settimeout( 1)
			self.sock.bind( (listenNetwork, listenPort))
			
			self.isConnected = True
			self.connected = False
		
		except Exception as e:
			self.error( e)
			self.isConnected = False
			self.connected = False
			return
			
		self.listening()
		
		while not XTension.isShuttingDown:
		
			try:
				workMessage, workAddress = self.sock.recvfrom( 4096)
				
			except socket.timeout:
				continue
			except Exception as e:
				if XTension.isShuttingDown:
					sys.exit()
					return
				
				self.error( e)
			
			self.remoteAddress = workAddress
			self.buffer = workMessage
			try:
				self.dataAvailable()
			except Exception as e:
				XTension.writeLog( "error in datagramReceived: %s" % e, xtLogRed)
				XTension.writeLog( traceback.format_exc(), xtLogRed)
				continue
						

	
		
			
	#
	#	MAKE TCP CONNECTION
	#
	
	def makeTCPConnection( self):
		TCP_KEEPALIVE = 0x10
		try:
			self.sock = socket.socket( socket.AF_INET, socket.SOCK_STREAM)
			self.sock.setsockopt( socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
			self.sock.setsockopt( socket.IPPROTO_TCP, TCP_KEEPALIVE, 5) #TEMPORARILY changing this to 5 seconds to see if it times out more quickly
			self.sock.settimeout( 10) # 10 second timeout on initial connection
		
			workAddress = self.getParm( xtKeyRemoteAddress)
			workPort = int( self.getParm( xtKeyRemotePort))
		
			XTension.debugLog( "connecting to: %s:%s" % (workAddress, str( workPort)))
			
			self.sock.connect( (workAddress, workPort))				
			XTension.debugLog( "connected OK")
			
			self.sock.settimeout( 1) # 1 second timeout after that so we can catch shutdown messages from XTension
			
			# clear the buffer
			self.buffer = ''
			
			# protect our call to connected in case subclass code throws an unexpected error
			try:
				self.eventConnected()
			except Exception as f:
				XTension.writeLog( "Error in XTRemoteConnection.connected %s" % f, xtLogRed)
				
			
			
			# these logging and setting the runstate should be done in the new connected event now
			#XTension.debugLog( "Connected to " + XTension.settings.get( xtKeyRemoteAddress) + ":" + str( XTension.settings.get( xtKeyRemotePort)))

			# tell XTension that we are connected again if there had been an error in the past. This makes sure the status in XTension is green and shows who we are connected to
			#XTension.setRunState( xtRunStateOK, "Connected to: " + XTension.settings.get( xtKeyRemoteAddress) + ":" + str( XTension.settings.get( xtKeyRemotePort)))
						
			return True
			
		except Exception as e:

			self.sock = None
			if self.errorSent == False:
				self.errorSent = True
				
				# protect our call to the error handler
				try:
					self.error( e)
				except Exception as f:
					XTension.writeLog( "Error in XTRemoteConnection.makeTCPConnection( %s) and a further error in XTRemoteConnection.error %s" % (e, f), xtLogRed) 
				
				
			return False
	
	#
	#	getParm
	#
	#	used through this class to get a configuration value either from your overridden 
	# 	values dictionary passed to the constructor or from xtension.settings if you are not
	# 	overriding it.
	#
	# updated to also look in the XTension.info dictionary as loaded from the info.json file for the plugin
	# as some, non-user configuration constants might be there. But that is the case only if no default is passed
	#
	#
	
	def getParm( self, key, default=None):
	
		if key in self.overrideParms:
			return self.overrideParms[ key]

		elif XTension.settings.exists( key):
			return XTension.settings[ key]

		elif XTension.info != None and key in XTension.info:
				return XTension.info[key]
		else:
			return default

		
				
	#
	#	WRITE
	#
	#	writes the outgoing data to whatever connection method is selected
	#	if you're sending a UDP datagram then also include the standard tuple of
	#	(ipaddress, port) in the toAddress field
	#
	def write( self, theData, toAddress=None):
	
		
		
# 		if self.sock == None:
# 			XTension.writeLog( "attempt to send data with no connection: %s" % theData, xtLogRed)
# 			self.error( 'no connection')
# 			return False

		self.writeLock.acquire()
		
		#
		#	OUTGOING TCP
		#
		
		if self.connectionMethod == xtPortNameOutgoingTCP:
			totalsent = 0
			while totalsent < len( theData):
				try:
					sent = self.sock.send( theData[ totalsent:])
				
					if sent == 0:
						self.writeLock.release()
						return False
					
					totalsent += sent
				except Exception as e:
					self.writeLock.release()
					self.error( e)
					return False
			self.writeLock.release()
			return True
			
		#
		#	local serial port
		#
		elif self.serialPort != None:
		
			try:
				self.serialPort.write( theData)
				self.writeLock.release()
				return True

			except Exception as e:
				self.writeLock.release()
				self.error( e)
				return False
				
		
		
			
		#
		#	INCOMING UPD
		#
		elif self.listenType == xtKeyListenTypeUDP:
			
			try:
				self.sock.sendto( theData, toAddress)
				
			except Exception as e:
				self.writeLock.release()
				self.error( e)
				return False
			
			self.writeLock.release()
			return True
			
			
				
			
						
						







	#
	#	 SUBCLASS THESE OUTGOING HANDLERS
	#	in order to process the events
	#	these are for outgoing connections only
	# 	the server related events that pass you an instance to the actual
	#	socket object are below. They different for TCP or UDP connections
	
	
	#
	#	CONNECTED EVENT
	#
	# remember that the class has an "isConnected" boolean that is not the same as this event
		
	def eventConnected( self):
		#subclass this to get your connected event, you should do at least this much:
			theMessage = "Connected to %s:%s" % (XTension.settings.get( xtKeyRemoteAddress), str( XTension.settings.get( xtKeyRemotePort)))
			XTension.debugLog( theMessage)
			XTension.setRunState( xtRunStateOK, theMessage)
	
	#
	#	ERROR
	#
	#	return True to make the super class be silent about this that you handled it
	# 	if you return nothing or False then it will do a stack trace from here
	# 	something like this that you should be subclassing
	#
	def error( self, e):
		
		XTension.writeLog( "XTRemoteConnection.error( %s)" % e, xtLogRed)
		XTension.setRunState( xtRunStateError, str( e))
		return True
		
	#
	#	DATA AVAILABLE
	#
	def dataAvailable( self):
		XTension.writeLog( "received new data, check self.buffer")
		
	#
	#	LISTENING
	#
	# for an incoming connection you'll get this event once when the server is ready for connections
	
	def listening( self):
		XTension.writeLog( "listening server is now ready for connections")
	
	
#
# for incoming connections 
# subclass this class and provide the XTRemoteConnection class with a
# makeTCPClient() handler that returns a new instance of the correct class
#


class XTTCPServerConnection( threading.Thread):
	
	# called by the server thread after you return the new class
	# could do this in the constructor but then you'd have to remember to call the 
	# super constructor which is not necessary if we do this
	def _setup( self, ip, port, sock, myServer):
		self.ip = ip
		self.port = port
		self.sock = sock
		self.parentServer = myServer
		
		self.buffer = ''
		self.isConnected = True
		self.connected = True
		self.writeLock = threading.Lock() 

		self.start()

		
	def run( self):
	
		self.sock.settimeout( 1)
		
		self.eventConnected()
		
		while not XTension.isShuttingDown:
		
			try:
				newData = self.sock.recv( 2048)
			
				if newData == '':
					self.isConnected = False
					self.connected = False
					self.error( 'disconnected')
				
					if self in parentServer.connectedThreads:
						del parentServer.connectedThreads[ self]
				
					sys.exit()
					return
			
			except socket.timeout:
				# no error, just checking to make sure that we're not being shutdown
				continue
				
			except Exception as e:
				
				self.isConnected = False
				self.connected = False
				self.error( e)
				
				if self in parentServer.connectedThreads:
					del parentServer.connectedThreads[ self]
					
				sys.exit()
				return
				
			self.buffer += newData
			
			try:
				self.dataAvailable()
			except Exception as e:
				XTension.writeLog( "error in XTTCPServerThread.dataAvailable %s" % e)
	
				
	#
	#	WRITE
	#
	#	sends the data down the socket
	#
	def write( self, theData):
	
		if not self.connected or self.sock == None:
			XTension.writeLog( "write to disconnected socket", xtLogRed)
			return
			
			
		

		self.writeLock.acquire()
		

		totalsent = 0
		while totalsent < len( theData):
			try:
				send = self.sock.send( theData[ totalsent:])
				
				if sent == 0:
					self.writeLock.release()
					if XTension.isShuttingDown:
						sys.exit()
						return
					else:
						self.error( 'error in write to socket')
						return
							
				totalsent += sent
						
			except Exception as e:
				self.writeLock.release()
				
				if XTension.isShuttingDown:
					sys.exit()
					return
				else:
					self.error( e)
					return
						
		self.writeLog.release()				

			
	

					
	#
	# SUBCLASS THESE METHODS TO HANDLE EVENTS IN THIS THREAD
	#
	
	#
	#	CONNECTED EVENT
	#
	def connected( self):
		XTension.writeLog( "Accepted Connection from: %s:%s" & (self.ip, str( self.port)))
		
	#
	#	DATA AVAILABLE
	#
	def dataAvailable( self):
		XTension.writeLog( "received new data, check self.buffer")
	
	#
	#	ERROR
	#
	
	def error( self, e):
		XTension.writeLog( "Error on socket %s" % e)




#
# this is now used only if there is no valid IP address in the XTEnsion settings object
#
def getIp():
	s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
	try:
		s.connect(('10.255.255.255', 1))
		IP = s.getsockname()[0]
	except Exception as e:
		#IP = '127.0.0.1'
		XTension.writeLog( "unable to resolve a local IP address: " + str( e), xtLogRed)
		XTension.setRunState( xtRunStateFail, "unable to resolve a local address")
		XTension.setStatus( "unable to resolve network address")
		sys.exit()

	finally:
		s.close()
		return IP

#
#	XTFloat
#
# for localized systems that use a comma instead of a period to delineate the decimal point
# just passing that to float() causes an error. This is a safe routine to replace any 
# commas with periods before converting or verifying that it's a float
# this should be used instead of any other cast to float() that you make. Or at some point
# I'll figure out the proper localization of python but that may add other oddnesses
#

def xtFloat( inValue):

	#XTension.writeLog( "inValue (%s) type=%s" % (inValue, type( inValue)))

	try:
		if type( inValue) == bytes:
			inValue = inValue.decode()
			
		elif type( inValue) == float:
			return inValue
			
		elif type( inValue) == int:
			return inValue
			
		#XTension.writeLog( "type of inValue=%s" % type( inValue))
				
		
		return float( inValue.replace( ',', '.'))
	except Exception as e:
		XTension.writeLog( "Unable to safely convert %s to a floating point value (%s)" % (inValue, str( e)), xtLogRed)
		XTension.writeLog( traceback.format_exc(), xtLogRed)
# 		return inValue
		# TEMPORARY changed this to raise an exception so that we can tell where it was raised later
		raise e
		
#
#	xtInt
#
# integers can often have a decimal after them which blows up the conversion from string to int 
# and they may also be commas on localized systems with that set which python2 does not handle properly
# so here we do something similar to the xtFloat method above. This just calls the float method above and then
# casts the result as an integer before returning
#

def xtInt( inValue):
	try:
		return int( xtFloat( inValue))
	except Exception as e:
		XTension.writeLog( "Unable to safely convert %s to an integer (%s)" % (inValue, str( e)), xtLogRed)
		XTension.writeLog( traceback.format_exc(), xtLogRed)
		return inValue
		
		
#
#	MAP
#
# just like the arduino map command but for mapping values in python. For converting a 0-100%
# value to the actual output of the device and so forth. Use with the min/max values of the unit to map
# the values if necessary.

def xtMap( x, in_min, in_max, out_min, out_max):
	return (x - in_min) * (out_max - out_min) / (in_max - in_min) + out_min






#
#
#	base36encode
#
#	used to turn the id and pin numbers into the proper url value to
#	encode into the qrcode
#
def base36Encode( number):

	# make sure it's a number as most things in XTension are strings
	number = int( number)


	alphabet, base36 = ['0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ', '']
	
	while number:
		number, i = divmod( number, 36)
		base36 = alphabet[i] + base36
		
	return base36 or alphabet[0]

#
#	SHORT WEEKDAY NAME
#
# 	the index from xtension starts with 0 being Sunday but python dates
#	use 0 as Monday and 6 as Sunday so we adjust for that to make it easier
#
def xtShortWeekdayName( index):
	index += 1
	if index > 6:
		index = 0
		
	return XTension.settings.get( xtKeyShortWeekdayNames).split( ',')[ index]
	
#
#	LONG WEEKDAY NAME
#
#	see short weekday name
def xtLongWeekdayName( index):
	index += 1
	if index > 6:
		index = 0

	return XTension.settings.get( xtKeyLongWeekdayNames).split( ',')[index]
	
#
#	RELATIVE DAY NAME
#
#	returns yesterday for yesterday, Today for today, Tomorow for tomorrow and 
#	then the long or short weekday names for the rest of the week. Not yet any good
#	for days longer ago in the past or days further in the future than a week from now
def xtRelativeWeekdayName( inDate, useLongNames = False):
	today = datetime.today()
	
	todayTuple = today.timetuple()
	inTuple = inDate.timetuple()

	dayDifference = (inTuple.tm_year + inTuple.tm_yday) - (todayTuple.tm_year + todayTuple.tm_yday)
	
	if dayDifference == -1:
		return "Yesterday"
	elif dayDifference == 0:
		return "Today"
	elif dayDifference == 1:
		return "Tomorrow"
	elif dayDifference < 8:
		if useLongNames:
			return inDate.strftime( '%A')
		else:
			return inDate.strftime( '%a')
	else:
		return inDate.strftime( '%x')


#
#	F O R M A T   T I M E
#
#	takes a datetime object and returns a string with the time formatted either as 24 hour
#	or with am/pm as the system is setup
#	tags are {hour} {minute} {seconds} {ampm}
# kwargs allow you to pass midnightnoon=True and if thats there then if your date is equal to those
# then it will replace the output with the words midnight or noon
#

def xtFormatTime( inDate, inFormat=None, **kwargs):

	if inFormat == None:
		rawString = "{hour}:{minute}:{seconds}{ampm}"
	else:
		rawString = inFormat

	if 'midnightnoon' in kwargs:
		useDescription = kwargs['midnightnoon']
	else:
		useDescription = False

		
	minuteData = '{:02d}'.format( inDate.minute)
	secondsData = '{:02d}'.format( inDate.second)
		
	if XTension.data.get( xtKeyUse24HourTime, False):
		hourData = inDate.hour
		
		if useDescription:
			if hourData == 0 and inDate.minute == 0 and inDate.second == 0:
				return 'midnight'
			elif hourData == 12 and inDate.minute == 0 and inDate.second == 0:
				return 'noon'		
		
		ampmData = ''
	else:
	
		if inDate.hour == 0:
			if useDescription and inDate.minute == 0 and inDate.second == 0 :
				rawString = 'midnight'

			hourData = 12
			ampmData = 'am'
			
		elif inDate.hour == 12:
			if useDescription and inDate.minute == 0 and inDate.second == 0:
				rawString = 'noon'

			hourData = 12
			ampmData = 'pm'
			
		elif inDate.hour > 12:
			hourData = inDate.hour - 12
			ampmData = 'pm'
			
		else:
			hourData = inDate.hour
			ampmData = 'am'

	return rawString.format( hour=hourData, minute=minuteData, seconds=secondsData, ampm=ampmData)
	
	
	
	
	
#
#
#		H E X I F Y 
#
#	just a nice formatting method for logging a string of binary data as hex for debugging
#

def hexify( data):
	#return ' '.join( '{:02x}'.format( x) for x in data)
	
	count = len( data)
	out = ''
	
	if isPy3:
		data = BytesIO( data)
	else:
		data = io.BytesIO( data)
	
	for i in range( count):
		x = unpack( "B", data.read( 1))[0]
		#print( "reading (%s) %s" % (x, type( x)))
		out += " x%s(%s)" % (format( x, '02x').upper(), x)
	
	data.close()
		
	return out
	









#
#		class 		X T   D E F E R R E D   C O M M A N D
#
#	
#	this was originally part of the hubitat plugin but may be useful elsewhere so I moved it to the
#	plugin code to be available to everything. 
#	
#	it is sometimes the case that many updates for a unit will come in in separate requests or packets and it
#	is necessary to build up a command to XTension after all the data has been received. If simple
#	timing is all that is needed to do this properly then this deferred command class may be of help
#	
#	pass a reference to the parent xtUnit subclass as it will use it's xtUnit.sendCommand method to 
#	actually send the command. 
#
#	any calling of addData of data to the command will result in a timer starting and however much data has been added to the
#	command by the time half a second is elapsed it will send the command. If no xtKeyCommand has been set then
#	a NoOp is added so that the command has an actual commmand as that is required but handled autoatically here
#	this can also be useful for sending multiple unit properties via the addUnitProperty method.
#
#	this class can be reused, it is not necessary to create a new one for each command. Create just one and use it
#	as often as needed.
#	
#	additionally you can change the timeout by passing timeout=2.0 or whatever number of seconds you'd like 
#	to wait until it sends the command as built by then. It defaults to half a second.
# 	the timeout can be changed at any time after the class is created by setting the class property timeout
#	to whatever you wish, though it will not affect a command that has already been started. If the timer is not
#	already running then the next one will use the new value.

class xtDeferredCommand():
	#
	#		__ I N I T __
	#
	def __init__( self, inParentUnit, **kwds):

		self.parentUnit = inParentUnit
		self.command = None
		self.thread = None
		self.lock = threading.Lock()
		self.timeout = kwds.get( "timeout", 0.5)
		
	
	#
	#	A D D   D A T A 
	#
	#	this is the entry call to begin or add to a command
	#
	#	can pass "conditional=True" to not change one that is already there
	#	useful for the command in case we receive the level first and then the switch on later
	#	we don't want to replace the setValue command with an on command in that place
	#	but we do if we receive the on and then the set level later
	#
	def addData(self, **kwds):
		self.lock.acquire()
		isConditional = False

		try:		
			if "conditional" in kwds:
				isConditional = kwds[ "conditional"]
				# and then remove this as we don't want to send it to XTension
				del( kwds[ "conditional"])
		

			# if the command is None then we have no outstanding command and we should create one
			if self.command == None:
				# all commands must have a command reference in them so start it with the NoOp
				# so if some of the data does not trigger an on or off it will still br properly 
				# published
				self.command = {}
			
				# now transfer all the remaining keys from kwds into the command dict
				for key in kwds:
					# if conditional then dont add it if it's already there
					if isConditional and key in self.command:
						continue
					
					self.command[ key] = kwds[ key]
			
				self.thread = Thread( target=self.deferredSend, args=())
				self.thread.start()
			else:
				# our command is outstanding so we can instead just add any passed key to it
				for key in kwds:
					if isConditional and key in self.command:
						continue
						
					self.command[ key] = kwds[ key]
		except Exception as e:
			XTension.writeLog( "error in deferredCommand.addData( %s)" % e, xtLogRed)
			XTension.writeLog( traceback.format_exc(), xtLogRed)
			
		# the try block above assures that the release gets called even if an error happens
		self.lock.release()
	
	
	#
	#	A D D   H U E
	#
	#	added specifically for the hubbitat but might be usefull elsewhere
	#	since the updates come in many individual calls and not all at once you won't have the
	#	hue and saturation of a color all at the same time so you need to be able to set them
	#	but to XTension the HSV value is a single entry. Rather than handle this in the plugin
	#	I've added this handling to the plugin standard functions
	#
	# hue must be between 0 and 1 for XTension
	def addHue( self, newHue):
		self.lock.acquire()
		
		if self.command == None:
			self.command = {}
			self.thread = Thread( target=self.deferredSend, args=())
			self.thread.start()
			
		
		if xtKeyColorHSV in self.command:
			[workHue, workSaturation, workValue] = self.command[ xtKeyColorHSV].split( ',')
			
			
			self.command[ xtKeyColorHSV] = ','.join( [str( newHue), workSaturation, workValue])
			
		else:
			self.command[ xtKeyColorHSV] = ','.join( [str( newHue), "1", "1"])
			
		self.lock.release()
		
	
	#
	#	A D D   S A T U R A T I O N
	#
	#	see the addHue command above for discussion
	#
	# sats must be between 0 and 1 for XTension
	def addSaturation( self, newSat):
		self.lock.acquire()
			
		if self.command == None:
			self.command = {}
			self.thread = Thread( target=self.deferredSend, args=())
			self.thread.start()
			
		if xtKeyColorHSV in self.command:
			[workHue, workSaturation, workValue] = self.command[ xtKeyColorHSV].split( ',')
			
			self.command[ xtKeyColorHSV] = ','.join( [workHue, str( newSat), workValue])
		
		else:
			self.command[ xtKeyColorHSV] = ','.join( ["1", str( newSat), "1"])
			
		self.lock.release()
	
	
	#
	#	A D D   U N I T   P R O P E R T Y
	#
	#	sometimes you may wish to add multiple unit properties to a command and
	#	in that case you can call this any number of times and the lower level indexing is 
	#	taken care of automatically for you
	#
	#	up to 10 unit property key/value pairs can be added to the list
	#	since multiples can be received sometimes this also checks to make sure the key
	#	is not already in the command and if so later calls with the same key will replace
	#	the old one.
	#
	#	returns False if the key was not added because it is full
	
	def addUnitProperty( self, key, value):
		
		self.lock.acquire()
		
		try:
			if self.command == None:
				self.command = {}
				self.thread = Thread( target=self.deferredSend, args=())
				self.thread.start()
		
			for i in range( 0, 10):
				workNameKey = xtKeyUnitPropertyName + str( i)
			
				# if one is set by this name then check to be sure the unitPropertyName is not the same
			
				if workNameKey in self.command:
					if self.command[ workNameKey] == key:
						# replace the previous one with the new one
						self.command[ xtKeyUnitPropertyValue + str( i)] = value
						self.lock.release()
						return True
					# this one is already set, keep looking for a free spot
					continue
				else:
					# no key with this number was found, we can add it here
				
					self.command[ workNameKey] = key
					self.command[ xtKeyUnitPropertyValue + str( i)] = value
					self.lock.release()
					return True

		except Exception as e:
			XTension.writeLog( "Error: deferredCommand.addUnitProperty( %s)" % e, xtLogRed)
			XTension.writeLog( traceback.format_exc(), xtLogRed)
		
		# we went through all the available keys an there is no slot for another property to be added
		# 
		self.lock.release()
		return False
			
		

	#
	#	D E F E R R E D   S E N D
	#
	#	created when you start adding data to the command
	#	is running in a thread so the sleep command will not block other threads
	#	sleeps for half a second and then sends the command, clearing it afterwards so that
	#	a new one can be created after that.
	#	
	def deferredSend( self):
		sleep( self.timeout)
		
		try:
			self.lock.acquire()
		
			
			# make sure there is a command and if not use NoOp
			if not "xtKeyCommand" in self.command:
				# I believe this is actually incorrect, since these are keywords parameters
				# the name of it will be the string "xtKeyCommand" and not the value of it
				#self.command[ xtKeyCommand] = xtCommandNoOp
				self.command[ "xtKeyCommand"] = xtCommandNoOp


			#XTension.debugLog( "sending deferred command", xtLogGreen)			
			self.parentUnit.sendCommand( **self.command)
		
		except Exception as e:
			XTension.writeLog( "error in deferredCommand.deferredSend( %s)" % e, xtLogRed)
			XTension.writeLog( traceback.format_exc(), xtLogRed)

		# clear us out of the object so it can be used again
		self.command = None

		self.lock.release()

		#XTension.debugLog( "deferredSend complete", xtLogGreen)		
			





#
#	R G B   2   H S V
#	helper function that may be used by many plugins
#	
#	RGB values are [0,255] H is [0,360] S and V are [0,1]

def rgb2hsv(r, g, b):
	r, g, b = xtInt( r)/255.0, xtInt( g)/255.0, xtInt( b)/255.0

	mx = max(r, g, b)
	mn = min(r, g, b)
	df = mx-mn
	if mx == mn:
		h = 0
	elif mx == r:
		h = (60 * ((g-b)/df) + 360) % 360
	elif mx == g:
		h = (60 * ((b-r)/df) + 120) % 360
	elif mx == b:
		h = (60 * ((r-g)/df) + 240) % 360
	if mx == 0:
		s = 0
	else:
		s = df/mx
		v = mx
	return h, s, v
    

#
#	H S V   2   R G B
#
#	RGB values are [0,255] H is [0,360] S and V are [0,1]
def hsv2rgb(h, s, v):
	
	h, s, v = xtFloat( h), xtFloat( s), xtFloat( v)
#     h = xtFloat(h)
#     s = xtFloat(s)
#     v = xtFLoat(v)
    
	h60 = h / 60.0
	h60f = math.floor(h60)
	hi = int(h60f) % 6
	f = h60 - h60f
	p = v * (1 - s)
	q = v * (1 - f * s)
	t = v * (1 - (1 - f) * s)

	r, g, b = 0, 0, 0
	if hi == 0: r, g, b = v, t, p
	elif hi == 1: r, g, b = q, v, p
	elif hi == 2: r, g, b = p, v, t
	elif hi == 3: r, g, b = p, q, v
	elif hi == 4: r, g, b = t, p, v
	elif hi == 5: r, g, b = v, p, q

	r, g, b = int(r * 255), int(g * 255), int(b * 255)
	return r, g, b





	
#
#	MAIN
#
#	this is just for testing as we are included and TEMPORARY
#

# print( "XTension plugin is included")
# for s in sys.path:
# 	print( "          path=%s" % s)
	
	
#
#	SETUP CTYPES
#
#	TEMPORARY an attempt to make some lbrary linking more reliable


#def _setup_ctypes():
#from ctypes.macholib import dyld
#import os
#     frameworks = os.path.join(os.environ["RESOURCEPATH"], "..", "Frameworks")
#frameworks = os.environ[ "PYTHONFRAMEWORK"]
#print( "setting framework folder link to: %s" % frameworks)
# dyld.DEFAULT_FRAMEWORK_FALLBACK.insert(0, frameworks)
# 	dyld.DEFAULT_LIBRARY_FALLBACK.insert(0, frameworks)

# def _setup_ctypes():
# 	try:
# 		from ctypes.macholib import dyld
# 	except Exception as e:
# 		print( "ERROR loading ctypes.macholib (%s)" % e)
# 	
# 	frameworks = os.environ[ "PYTHONFRAMEWORK"]
# 	print( "===== frameworks folder is: %s" % frameworks)
# print( "================================= plugin was started")
#_setup_ctypes()
#print( "ctypes was fixed")