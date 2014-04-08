var sip=require('sip');
var util=require('util');

var log4js = require('log4js');
log4js.configure('log4j_config.json');
var myLogger = log4js.getLogger("sip_proxy");

//holds canceller method info for each req/res pair
var contexts = {};

function makeContextId(msg) {
    var via = msg.headers.via[0];
    return [
        via.params.branch,
        via.protocol,
        via.host,
        via.port,
        msg.headers['call-id'],
        msg.headers.cseq.seq
    ];
}

function defaultCallback(rs) {
    rs.headers.via.shift();
    exports.send(rs);
}

exports.send = function(msg, callback) {
    myLogger.debug("proxy#send");
    var ctx = contexts[makeContextId(msg)];

    if (!ctx) {
        sip.send.apply(sip, arguments);
        return;
    }

    return msg.method ?
        forwardRequest(ctx, msg, callback || defaultCallback) :
        forwardResponse(ctx, msg);
};


function forwardResponse(ctx, rs, callback) {
    myLogger.debug("proxy#forwardResponse");
    if (+rs.status >= 200) {
        delete contexts[makeContextId(rs)];
    }

    sip.send(rs);
}


function sendCancel(rq, via, route) {
    sip.send({
        method: 'CANCEL',
        uri: rq.uri,
        headers: {
            via: [via],
            to: rq.headers.to,
            from: rq.headers.from,
            'call-id': rq.headers['call-id'],
            route: route,
            cseq: {method: 'CANCEL', seq: rq.headers.cseq.seq}
        }
    });
}


function forwardRequest(ctx, rq, callback) {
    myLogger.debug("proxy#forwardRequest");
    var route = rq.headers.route && rq.headers.route.slice();
    sip.send(rq, function(rs, remote) {
        myLogger.debug("proxy#send sip.send callback");
        myLogger.debug(util.inspect(rs));
        if (+rs.status < 200) {
            var via = rs.headers.via[0];
            ctx.cancellers[rs.headers.via[0].params.branch] = function() {
                sendCancel(rq, via, route);
            };

            if (ctx.cancelled) {
                sendCancel(rq, via, route);
            }
        }
        else {
            delete ctx.cancellers[rs.headers.via[0].params.branch];
        }

        callback(rs, remote);
    });
}


function onRequest(rq, remote, callback) {
    var id = makeContextId(rq);
    contexts[id] = { cancellers: {} };

    try {
        callback(sip.copyMessage(rq), remote);
    } catch(e) {
        delete contexts[id];
        throw e;
    }
}


exports.start = function(options, onRequestCallback) {
    sip.start(options, function(rq, remote) {
        if (rq.method === 'CANCEL') {
            var ctx = contexts[makeContextId(rq)];

            if (ctx) {
                sip.send(sip.makeResponse(rq, 200));

                ctx.cancelled = true;
                if (ctx.cancellers) {
                    Object.keys(ctx.cancellers).forEach(function(c) {
                        ctx.cancellers[c]();
                    });
                }
            }
            else {
                sip.send(sip.makeResponse(rq, 481));
            }
        }
        else {
            onRequest(rq, remote, onRequestCallback);
        }
    });
};

exports.stop = sip.stop;

