**DER Encoding & Kerberos**


Kerberos consists of several exchanges:  

***AS Exchange***

The Authentication Service (AS) Exchange between the client and the
   Kerberos Authentication Server is initiated by a client when it
   wishes to obtain authentication credentials for a given server but
   currently holds no credentials.  In its basic form, the client's
   secret key is used for encryption and decryption.  This exchange is
   typically used at the initiation of a login session to obtain
   credentials for a Ticket-Granting Server, which will subsequently be
   used to obtain credentials for other servers without requiring further 
   use of the client's secret key. This exchange is also used to request 
   credentials for services that must not be mediated through the 
   Ticket-Granting Service, but rather require knowledge of a principal's secret key, 
   such as the password-changing service (the password-changing service denies requests
   unless the requester can demonstrate knowledge of the user's old
   password; requiring this knowledge prevents unauthorized password
   changes by someone walking up to an unattended session).

**Client to Kerberos KDC**

**KRB_KDC_REQ:** no application tag, but is incorporated into either KRB_AS_REQ for an initial ticket or KRB_TGS_REQ for an additional ticket.

**KRB_AS_REQ:** consists of client’s identity, server’s identity, supplementary credential metadata, and a randomly generated nonce to detect replays. 

```
AS-REQ          ::= [APPLICATION 10] KDC-REQ
TGS-REQ         ::= [APPLICATION 12] KDC-REQ
KDC-REQ         ::= SEQUENCE {
        pvno            [1] INTEGER (5) ,
        msg-type      [2] INTEGER (10 -- AS -- | 12 -- TGS --),
        padata          [3] SEQUENCE OF PA-DATA OPTIONAL
                            -- NOTE: not empty --,
        req-body        [4] KDC-REQ-BODY
}

PA-DATA         ::= SEQUENCE {
        padata-type     [1] Int32,
        padata-value    [2] OCTET STRING
}
```

PA-DATA stores pre-authentication data which is historically used to augment the initial authentication exchange.

**padata-type**<br>
      Indicates the way that the padata-value element is to be
      interpreted.  Negative values of padata-type are reserved for
      unregistered use; non-negative values are used for a registered
      interpretation of the element type.

**padata-value**<br>
      Usually contains the DER encoding of another type; the padata-type
      field identifies which type is encoded here.

      padata-type  Name             Contents of padata-value

      1            pa-tgs-req       DER encoding of AP-REQ

      2            pa-enc-timestamp DER encoding of PA-ENC-TIMESTAMP

      3            pa-pw-salt       salt (not ASN.1 encoded)

      11           pa-etype-info    DER encoding of ETYPE-INFO

      19           pa-etype-info2   DER encoding of ETYPE-INFO2

```
KDC-REQ-BODY    ::= SEQUENCE {
        kdc-options             [0] KDCOptions,
        cname                   [1] PrincipalName OPTIONAL
                                    -- Used only in AS-REQ --,
        realm                   [2] Realm
                                    -- Server's realm
                                    -- Also client's in AS-REQ --,
        sname                   [3] PrincipalName OPTIONAL,
        from                    [4] KerberosTime OPTIONAL,
        till                    [5] KerberosTime,
        rtime                   [6] KerberosTime OPTIONAL,
        nonce                   [7] UInt32,
        etype                   [8] SEQUENCE OF Int32 -- EncryptionType
                                    -- in preference order --,
        addresses               [9] HostAddresses OPTIONAL,
        enc-authorization-data  [10] EncryptedData OPTIONAL
                                    -- AuthorizationData --,
        additional-tickets      [11] SEQUENCE OF Ticket OPTIONAL
                                       -- NOTE: not empty
}
```



**Kerberos KDC to Client**

The KRB_KDC_REP message format is used for the reply from the KDC for
   either an initial (AS) request or a subsequent (TGS) request.  There
   is no message type for KRB_KDC_REP.  Instead, the type will be either
   KRB_AS_REP or KRB_TGS_REP.  The key used to encrypt the ciphertext
   part of the reply depends on the message type.  For KRB_AS_REP, the
   ciphertext is encrypted in the client's secret key, and the client's
   key version number is included in the key version number for the
   encrypted data.  For KRB_TGS_REP, the ciphertext is encrypted in the
   sub-session key from the Authenticator; if it is absent, the
   ciphertext is encrypted in the session key from the TGT used in the
   request.  In that case, no version number will be present in the
   EncryptedData sequence.

**KRB_AS_REP:** consists of a ticket for the client to present to the server, and (session key || matching nonce)_client’s SK.

```
   AS-REP          ::= [APPLICATION 11] KDC-REP

   TGS-REP         ::= [APPLICATION 13] KDC-REP

   KDC-REP         ::= SEQUENCE {
           pvno            [0] INTEGER (5),
           msg-type        [1] INTEGER (11 -- AS -- | 13 -- TGS --),
           padata          [2] SEQUENCE OF PA-DATA OPTIONAL
                                   -- NOTE: not empty --,
           crealm          [3] Realm,
           cname           [4] PrincipalName,
           ticket          [5] Ticket,
           enc-part        [6] EncryptedData
                                   -- EncASRepPart or EncTGSRepPart,
                                   -- as appropriate
   }

   EncASRepPart    ::= [APPLICATION 25] EncKDCRepPart

   EncTGSRepPart   ::= [APPLICATION 26] EncKDCRepPart

   EncKDCRepPart   ::= SEQUENCE {
           key             [0] EncryptionKey,
           last-req        [1] LastReq,
           nonce           [2] UInt32,
           key-expiration  [3] KerberosTime OPTIONAL,
           flags           [4] TicketFlags,
           authtime        [5] KerberosTime,
           starttime       [6] KerberosTime OPTIONAL,
           endtime         [7] KerberosTime,
           renew-till      [8] KerberosTime OPTIONAL,
           srealm          [9] Realm,
           sname           [10] PrincipalName,
           caddr           [11] HostAddresses OPTIONAL
   }

   LastReq         ::=     SEQUENCE OF SEQUENCE {
           lr-type         [0] Int32,
           lr-value        [1] KerberosTime
   }
```

TODO: explain the fields

```
Ticket          ::= [APPLICATION 1] SEQUENCE {
           tkt-vno         [0] INTEGER (5),
           realm           [1] Realm,
           sname           [2] PrincipalName,
           enc-part        [3] EncryptedData -- EncTicketPart
   }


EncTicketPart   ::= [APPLICATION 3] SEQUENCE {
           flags                   [0] TicketFlags,
           key                     [1] EncryptionKey,
           crealm                  [2] Realm,
           cname                   [3] PrincipalName,
           transited               [4] TransitedEncoding,
           authtime                [5] KerberosTime,
           starttime               [6] KerberosTime OPTIONAL,
           endtime                 [7] KerberosTime,
           renew-till              [8] KerberosTime OPTIONAL,
           caddr                   [9] HostAddresses OPTIONAL,
           authorization-data      [10] AuthorizationData OPTIONAL
   }

TicketFlags     ::= KerberosFlags
           -- reserved(0),
           -- forwardable(1),
           -- forwarded(2),
           -- proxiable(3),
           -- proxy(4),
           -- may-postdate(5),
           -- postdated(6),
           -- invalid(7),
           -- renewable(8),
           -- initial(9),
           -- pre-authent(10),
           -- hw-authent(11),
   -- the following are new since 1510
           -- transited-policy-checked(12),
           -- ok-as-delegate(13)
```

**sname**<br>
      This field specifies all components of the name part of the
      server's identity, including those parts that identify a specific
      instance of a service.

**enc-part**<br>
      This field holds the encrypted encoding of the EncTicketPart
      sequence.  It is encrypted in the key shared by Kerberos and the
      end server (the server's secret key), using a key usage value of
      2.

**flags**<br>
      This field indicates which of various options were used or
      requested when the ticket was issued.  The meanings of the flags
      are as follows:

**tkt-vno**<br>
      This field specifies the version number for the ticket format.
      This document describes version number 5.

**realm**<br>
      This field specifies the realm that issued a ticket.  It also
      serves to identify the realm part of the server's principal
      identifier.  Since a Kerberos server can only issue tickets for
      servers within its realm, the two will always be identical.

**key**<br>
      This field exists in the ticket and the KDC response and is used
      to pass the session key from Kerberos to the application server
      and the client.

**crealm**<br>
      This field contains the name of the realm in which the client is
      registered and in which initial authentication took place.

**cname**<br>
      This field contains the name part of the client's principal
      identifier.

**transited**<br>
      This field lists the names of the Kerberos realms that took part
      in authenticating the user to whom this ticket was issued.  It
      does not specify the order in which the realms were transited.

**authtime**<br>
      This field indicates the time of initial authentication for the
      named principal.  It is the time of issue for the original ticket
      on which this ticket is based.  It is included in the ticket to
      provide additional information to the end service, and to provide
      the necessary information for implementation of a "hot list"
      service at the KDC.  An end service that is particularly paranoid
      could refuse to accept tickets for which the initial
      authentication occurred "too far" in the past.

**starttime**<br>
      This field in the ticket specifies the time after which the ticket
      is valid.  Together with endtime, this field specifies the life of
      the ticket.  If the starttime field is absent from the ticket,
      then the authtime field SHOULD be used in its place to determine
      the life of the ticket.

**endtime**<br>
      This field contains the time after which the ticket will not be
      honored (its expiration time).  Note that individual services MAY
      place their own limits on the life of a ticket and MAY reject
      tickets which have not yet expired.  As such, this is really an
      upper bound on the expiration time for the ticket.

**renew-till**<br>
      This field is only present in tickets that have the RENEWABLE flag
      set in the flags field.  It indicates the maximum endtime that may
      be included in a renewal.  It can be thought of as the absolute
      expiration time for the ticket, including all renewals.

**caddr**<br>
      This field in a ticket contains zero (if omitted) or more (if
      present) host addresses.  These are the addresses from which the
      ticket can be used.  If there are no addresses, the ticket can be
      used from any location.  The decision by the KDC to issue or by
      the end server to accept addressless tickets is a policy decision
      and is left to the Kerberos and end-service administrators; they
      MAY refuse to issue or accept such tickets.  Because of the wide
      deployment of network address translation, it is recommended that
      policy allow the issue and acceptance of such tickets.

**authorization-data**<br>
      This field contains restrictions on any authority obtained on the
      basis of authentication using the ticket.  It is possible for any
      principal in possession of credentials to add entries to the
      authorization data field since these entries further restrict what
      can be done with the ticket.  Such additions can be made by
      specifying the additional entries when a new ticket is obtained
      during the TGS exchange, or they MAY be added during chained
      delegation using the authorization data field of the
      authenticator.
      The data in this field may be specific to the end service; the
      field will contain the names of service specific objects, and the
      rights to those objects.
```
AuthorizationData       ::= SEQUENCE OF SEQUENCE {
              ad-type         [0] Int32,
              ad-data         [1] OCTET STRING
      }
```
**ad-data**<br>
      This field contains authorization data to be interpreted according
      to the value of the corresponding ad-type field.

**ad-type**<br>
      This field specifies the format for the ad-data subfield.  All
      negative values are reserved for local use.  Non-negative values
      are reserved for registered use.

***CS Exchange***

The client/server authentication (CS) exchange is used by network
   applications to authenticate the client to the server and vice versa.
   The client MUST have already acquired credentials for the server
   using the AS or TGS exchange.


**Client to Application Server**

The KRB_AP_REQ message contains the Kerberos protocol version number,
   the message type KRB_AP_REQ, an options field to indicate any options
   in use, and the ticket and authenticator themselves.  The KRB_AP_REQ
   message is often referred to as the "authentication header".


```
   AP-REQ          ::= [APPLICATION 14] SEQUENCE {
           pvno            [0] INTEGER (5),
           msg-type        [1] INTEGER (14),
           ap-options      [2] APOptions,
           ticket          [3] Ticket,
           authenticator   [4] EncryptedData -- Authenticator
   }

   APOptions       ::= KerberosFlags
           -- reserved(0),
           -- use-session-key(1),
           -- mutual-required(2)
```


***TGS Exchange***

The TGS exchange between a client and the Kerberos TGS is initiated
by a client when it seeks to obtain authentication credentials for a
given server (which might be registered in a remote realm), when it
seeks to renew or validate an existing ticket, or when it seeks to
obtain a proxy ticket.  In the first case, the client must already
have acquired a ticket for the Ticket-Granting Service using the AS
exchange (the TGT is usually obtained when a client initially
authenticates to the system, such as when a user logs in).  The
message format for the TGS exchange is almost identical to that for
the AS exchange.  The primary difference is that encryption and
decryption in the TGS exchange does not take place under the client's
key.  Instead, the session key from the TGT or renewable ticket, or
sub-session key from an Authenticator is used.  As is the case for
all application servers, expired tickets are not accepted by the TGS,
so once a renewable or TGT expires, the client must use a separate
exchange to obtain valid tickets.

**DER**

Encodings are [Identifier octets] | [Length octets] | [Contents octets] | [End-of octets (not always present)]




- Post to GitHub wiki
- Add DER to rust / verus



