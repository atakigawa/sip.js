var sip=require('./sip');
var util=require('util');

var myLogger = {
    trace: function() {},
    debug: function() {},
    info: function() {},
    warn: function() {},
    error: function() {},
    fatal: function() {},
};

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

function defaultSendCancel(rq, rqPath, via, route) {
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
    }, rqPath);
}

exports.send = function(msg, msgPath, callback, onCancel) {
    myLogger.debug("proxy#send");
    var ctx = contexts[makeContextId(msg)];

    if (!ctx) {
        sip.send.apply(sip, arguments);
        return;
    }

    return msg.method ?
        forwardRequest(ctx, msg, msgPath,
                callback || defaultCallback,
                onCancel || defaultSendCancel) :
        forwardResponse(ctx, msg, msgPath);
};


function forwardResponse(ctx, rs, rsPath, callback) {
    myLogger.debug("proxy#forwardResponse");
    if (+rs.status >= 200) {
        delete contexts[makeContextId(rs)];
    }

    sip.send(rs);
}


function forwardRequest(ctx, rq, rqPath, callback, onCancel) {
    myLogger.debug("proxy#forwardRequest");
    var route = rq.headers.route && rq.headers.route.slice();

    sip.send(rq, rqPath, function(rs, flow) {
        myLogger.debug("proxy#forwardRequest sip.send callback");
        if (+rs.status < 200) {
            var via = rs.headers.via[0];
            ctx.cancellers[rs.headers.via[0].params.branch] = function() {
                onCancel(rq, rqPath, via, route);
            };

            if (ctx.cancelled) {
                onCancel(rq, rqPath, via, route);
            }
        }
        else {
            delete ctx.cancellers[rs.headers.via[0].params.branch];
        }

        callback(rs, flow);
    });
}


function onRequest(rq, flow, callback) {
    var id = makeContextId(rq);
    contexts[id] = { cancellers: {} };

    try {
        callback(sip.copyMessage(rq), flow);
    } catch(e) {
        delete contexts[id];
        throw e;
    }
}

function onCancelRequest(rq, flow) {
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
        sip.send(sip.makeResponse(rq, 481, 'Call Leg/Transaction Does Not Exist'));
    }
}

exports.start = function(options, onRequestCallback, optCallbacks) {
    if (options.proxyLogger) {
        myLogger = options.proxyLogger;
    }

    sip.start(
        options,
        function(rq, flow) {
            if (rq.method === 'CANCEL') {
                onCancelRequest(rq, flow);
            }
            else {
                onRequest(rq, flow, onRequestCallback);
            }
        },
        optCallbacks
    );
};

exports.stop = sip.stop;

