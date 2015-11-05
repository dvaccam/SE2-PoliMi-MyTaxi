abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}
/*
sig Float{
    leftPart: one Int,
    rightPart: one Int
}

sig GPSPos
{
	latitude: one Int,
	longitude: one Int
}
sig Date
{
	day: Int,
	month: Int,
	hour: Int,
	minute: Int
}

sig DriverList
{
	head : lone TaxiDriver,
	body: lone DriverList,
	tail: lone TaxiDriver
}

sig QueueList
{
	head : lone Queue,
	tail: lone QueueList
}

sig RqstForServList
{
	head : lone RqstForSrv,
	body: lone RqstForServList,
	tail: lone RqstForSrv
}

sig IncomingRqstList
{
	head : lone IncomingRqst,
	tail: lone IncomingRqstList
}

sig AcceptedRqstList
{
	head : lone AcceptedRqst,
	tail: lone AcceptedRqstList
}
*/
sig Code, Destination, Origin{}


sig TaxiDriver
{
//	username: one String,
//	password: one String,
//	code: one Code,
	availability: one Bool,
//	position: one GPSPos,
	incRqst: lone IncomingRqst
}

sig Passenger
{
//	email: one String,
//	position: one GPSPos,
	rqst: lone RqstForSrv
}


sig RqstForSrv
{
//	destination: one Destination,
//	time: one Date,
//	numPeople: one Int,
//	origin: one Origin,
	sharing: one Bool
//	sharingRadius: lone Float,
//	email: one String
}

sig IncomingRqst
{
//	destination: some Destination,
//	fee: one Float,
//	time: one Date,
//	numPeople: one Int,
//	origin: some Origin,
	rqsts: some RqstForSrv,
	accepted: set AcceptedRqst
}

sig AcceptedRqst
{
//	arrivalTime: one Date,
//	destination: some Destination,
//	fee: one Float,
//	numPeople: one Int,
//	origin: some Origin,
//	taxiCode: one Code,
//	incRqst: one IncomingRqst
}

sig MyTaxiService
{
//	queues: one QueueList,
	all_rqsts: set RqstForSrv,
	all_incoming: set IncomingRqst,
	all_accepted: set AcceptedRqst
}
/*
sig Queue
{
	zone: one String,
	drivers: one DriverList
}
*/






fact
{
	#MyTaxiService = 2
	#True = 1
	#False = 1

	all r: RqstForSrv {some m:MyTaxiService | r in m.all_rqsts}
	all r: IncomingRqst {some m:MyTaxiService | r in m.all_incoming}
	all r: AcceptedRqst {some m:MyTaxiService | r in m.all_accepted}

	all r: RqstForSrv { one p:Passenger | r in p.rqst}
	all r: RqstForSrv { one i:IncomingRqst | r in i.rqsts}
	all a: AcceptedRqst{ one i:IncomingRqst | a in i.accepted}
 	all i:IncomingRqst { one d:TaxiDriver | i in d.incRqst}
	all i:IncomingRqst { #i.accepted > 0 implies #i.accepted = #i.rqsts}
	all m:MyTaxiService, i:m.(m<:all_incoming),  r:m.(m<:all_rqsts), a:m.(m<:all_accepted) { a in m.all_accepted and r in m.all_rqsts}
	all t:TaxiDriver | t.availability = True and #t.incRqst > 0 implies #t.incRqst.accepted = 0
}


pred passengerSendsRequest[m, m': MyTaxiService, p, p':Passenger, r: RqstForSrv]
{
	r not in m.all_rqsts
	r not in p.rqst
	p'.rqst = p.rqst + r
	m'.all_rqsts = m.all_rqsts + r
}

pred driverReceivesRequest[m, m': MyTaxiService, t, t': TaxiDriver, i:IncomingRqst]
{
	m'.all_incoming = m.all_incoming + i
	t'.incRqst = t.incRqst + i
}

pred driverAcceptsRequest[m, m': MyTaxiService, t, t':TaxiDriver, a:AcceptedRqst]
{
	m'.all_accepted = m.all_accepted + a
	t'.incRqst.accepted = t.incRqst.accepted + a
	t'.availability = False
}

pred driverDeclinesRequest[t:TaxiDriver]
{
	t.incRqst = none
}

pred passengerCancelsAcceptedRequest[m, m': MyTaxiService, p: Passenger]
{
	m'.all_rqsts = m.all_rqsts - p.rqst
	m'.all_incoming = m.all_incoming - (m.all_incoming<:rqsts).(p.rqst)
	m'.all_accepted = m.all_accepted - (m.all_incoming<:rqsts).(p.rqst).accepted
}



pred show{}


run passengerSendsRequest
