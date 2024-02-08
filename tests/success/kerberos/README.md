**DER Encoding & Kerberos**


Kerberos consists of several exchanges:  


**Client to Kerberos KDC**

**KRB_AS_REQ:** consists of client’s identity, server’s identity, supplementary credential metadata, and a randomly generated nonce to detect replays.


**KRB_KDC_REQ:** no application tag, but is incorporated into either KRB_AS_REQ for an initial ticket or KRB_TGS_REQ for an additional ticket.
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

**padata-type**<br>
      Indicates the way that the padata-value element is to be
      interpreted.  Negative values of padata-type are reserved for
      unregistered use; non-negative values are used for a registered
      interpretation of the element type.

**padata-value**<br>
      Usually contains the DER encoding of another type; the padata-type
      field identifies which type is encoded here.

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

**KRB_AS_REP:** consists of a ticket for the client to present to the server, and (session key || matching nonce)_client’s SK.
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


**DER**

Encodings are [Identifier octets] | [Length octets] | [Contents octets] | [End-of octets (not always present)]




- Post to GitHub wiki
- Add DER to rust / verus



