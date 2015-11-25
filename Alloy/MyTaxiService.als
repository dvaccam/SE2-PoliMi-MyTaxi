//Boolean values
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

//A zone of the city
sig Zone{}

//A taxi driver
sig TaxiDriver
{
 	availability: one Bool,
	position: one Zone,
	incRqst: lone IncomingRqst
}

//A passenger
sig Passenger
{
	rqst: lone RqstForSrv,
	accept: lone AcceptedRqst
}

//A request for service
sig RqstForSrv
{
 	destination: one Zone,
	origin: one Zone,
	sharing: one Bool
}

//An incoming request
sig IncomingRqst
{
	destinations: some Zone,
	origins: some Zone,
	rqsts: some RqstForSrv,
	accepted: set AcceptedRqst
}

//An accepted request
sig AcceptedRqst
{
	a_destination: one Zone,
	a_origin: one Zone
}

//The MyTaxiService system
sig MyTaxiService
{
	all_rqsts: set RqstForSrv,
	all_incoming: set IncomingRqst,
	all_accepted: set AcceptedRqst
}


fact
{
	#MyTaxiService = 1
	#True = 1
	#False = 1

	//Every incoming or accepted request belongs to some MyTaxiService
	all r: IncomingRqst { some m:MyTaxiService | r in m.all_incoming }
	all r: AcceptedRqst { some m:MyTaxiService | r in m.all_accepted }

	//Every request for service belong to exactly one passenger and at most one incoming request
	all r: RqstForSrv {{ one p:Passenger | r in p.rqst} and {lone i:IncomingRqst| r in i.rqsts} /*and #rqsts.r <=2*/}

	//all r: RqstForSrv {some i:IncomingRqst| r in i.rqsts} and #rqsts.r <=2 and }

	//Every accepted request belongs to exactly one incoming request and exactly one passenger
	all a: AcceptedRqst { one i:IncomingRqst, p:Passenger | a in i.accepted and a in p.accept}

	//Every incoming request belongs to at most one taxi driver
 	all i: IncomingRqst { lone d:TaxiDriver | i in d.incRqst }
	
	//If an incoming request is accepted, it generates as much accepted requests as requests for service, and has been taken by one taxi driver
	all i: IncomingRqst { #i.accepted > 0 implies #i.accepted = #i.rqsts and {one t:TaxiDriver | i in t.incRqst}}

	//If a driver has an incmoming request and has not accepted then he is available
	all t:TaxiDriver {#t.incRqst > 0 and #t.incRqst.accepted = 0 implies t.availability = True}

	//If a driver has accepted a request he is no longer available
	all t:TaxiDriver {#t.incRqst.accepted > 0 implies t.availability = False}
	
	//If a driver has an incoming request, he is in the same zone of one of its origins
	all t:TaxiDriver{#t.incRqst > 0 implies t.position in t.incRqst.origins}
	
	//Every accepted requests belongs to the same MyTaxiServices of its incoming request 
	all i: IncomingRqst, a:i.accepted {all_accepted.a in all_incoming.i and i.accepted.a_origin = i.origins and i.accepted.a_destination = i.destinations }

	//Every incoming request belongs to the same MyTaxiServices of its requests for service
	all i: IncomingRqst, r:i.rqsts { all_incoming.i in all_rqsts.r and i.rqsts.origin = i.origins and i.rqsts.destination = i.destinations }

	//Every accepted request is related to exactly one request for service through the passenger
	all a: AcceptedRqst{ one r:accepted.a.rqsts | accept.a = rqst.r}

	//Not sharing incoming requests have only one request for service
	all i:IncomingRqst{ (some r:i.rqsts | r.sharing = False) implies #i.rqsts = 1}
}



//Creation of a requests
pred passengerCreateRequest[p,p':Passenger, r: RqstForSrv]
{
	p'.rqst-p.rqst=r
}
//run passengerCreateRequest



//Sending a request
pred passengerSendsRequest[m, m': MyTaxiService, r: RqstForSrv]
{
	m.all_incoming=m'.all_incoming
	m.all_accepted=m'.all_accepted
	r in m'.all_rqsts - m.all_rqsts
}
//run passengerSendsRequest



//All sent requests were created
assert sentWereCreated
{
	all  m, m': MyTaxiService, r: RqstForSrv | passengerSendsRequest[m, m', r] implies {one p:Passenger | p.rqst=r}
}
//check sentWereCreated



//Processing a request
pred processRequest[m, m': MyTaxiService, r: RqstForSrv, i:IncomingRqst]
{
	r in i.rqsts
	r in m.all_rqsts & m'.all_rqsts
	i in m'.all_incoming - m.all_incoming
}
//run processRequest



//Receiving an incoming request by the driver
pred driverReceivesRequest[t, t': TaxiDriver, i:IncomingRqst]
{
	t.position = t'.position
	t.availability = t'.availability
	t.availability = True
	i = t'.incRqst - t.incRqst
}
//run driverReceivesRequest



//All the incoming requests where processed
assert incomingWereProcessed
{
	all t, t': TaxiDriver, i:IncomingRqst |
	driverReceivesRequest[t, t', i] implies {some m:MyTaxiService | i in m.all_incoming}
}
//check incomingWereProcessed



//All requests are sent to a driver in the same zone
assert requestSentCorrectly
{
	all t, t':TaxiDriver, i:IncomingRqst |
	driverReceivesRequest[t, t', i] implies incRqst.i.position in i.origins
}
//check requestSentCorrectly


//A driver accepts a request
pred driverAcceptsRequest[m, m': MyTaxiService, t,t':TaxiDriver, i, i':IncomingRqst, a: some AcceptedRqst]
{
	i'.rqsts = i.rqsts
	i'.destinations = i.destinations
	i'.origins = i.origins
	i'.accepted - i.accepted = a	
	
	m.all_rqsts = m'.all_rqsts
	m'.all_incoming = m.all_incoming - i + i'
	m'.all_accepted - m.all_accepted = a

	t.position = t'.position
	t'.availability = False
	t.availability = True
	t.incRqst = i
	t'.incRqst = i'
}
//run driverAcceptsRequest



//Not sharing incoming requests only have one request for service
assert notSharingCorrect
{
	all i:IncomingRqst {#i.rqsts > 1 implies {all r:i.rqsts | r.sharing = True} }
}
//check notSharingCorrect



//Requests are zone-coherent
assert requestsZoneCoherent
{
	all i:IncomingRqst |
	{i.rqsts.origin = i.origins and i.rqsts.destination = i.destinations and 
	(#i.accepted > 0 implies (i.accepted.a_origin = i.origins and i.accepted.a_destination = i.destinations))}
}
//check requestsZoneCoherent
