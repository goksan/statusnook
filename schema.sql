begin transaction;

create table meta(
    id integer primary key,
    name text not null unique,
    value text not null
);

insert into
    meta(name, value)
values
    ('setup', 'domain');

create table user(
    id integer primary key,
    username text not null unique,
    password text not null
);

create table session(
    id integer primary key,
    token text not null unique,
    csrf_token text not null unique,
    user_id int references user(id) not null
);

create table service(
    id integer primary key,
    name text not null,
    helper_text text not null
);

create table severity(severity text not null);

insert into
    severity(severity)
values
    ('blue');

create table alert(
    id integer primary key,
    title text not null,
    type text not null,
    severity text not null,
    created_at datetime not null,
    ended_at datetime
);

create table alert_message(
    id integer primary key,
    content text not null,
    created_at datetime not null,
    last_updated_at datetime,
    alert_id int references alert(id) on delete cascade not null
);

create table alert_subscription(
    id integer primary key,
    type text not null,
    destination text not null collate nocase,
    meta text,
    active int not null default true,
    unique(type, destination)
);

create table alert_notification(
    id integer primary key,
    created_at datetime not null,
    sent_at datetime,
    alert_subscription_id int references alert_subscription(id) on delete cascade not null,
    alert_message_id int references alert_message(id) on delete cascade not null
);

create table alert_setting(
    id integer primary key,
    name text not null unique,
    value text not null
);

create table alert_setting_smtp_notification(
    id integer primary key,
    notification_channel_id int references notification_channel(id) on delete cascade not null unique
);

create table pending_email_alert_subscription(
    id integer primary key,
    token string not null,
    email text not null collate nocase,
    created_at datetime not null,
    confirmed_at datetime
);

create table alert_service(
    id integer primary key,
    alert_id int references alert(id) on delete cascade not null,
    service_id int references service(id) on delete cascade not null
);

create table monitor(
    id integer primary key,
    name text not null,
    url text not null,
    method text not null,
    frequency integer not null,
    timeout integer not null,
    attempts integer not null,
    request_headers text,
    body_format text,
    body text
);

create table monitor_log(
    id integer primary key,
    started_at datetime not null,
    ended_at datetime not null,
    response_code integer,
    error_message text,
    attempts integer not null,
    result text not null,
    monitor_id int references monitor(id) on delete cascade not null
);

create index idx_monitor_log_monitor_id_started_at on monitor_log(monitor_id, started_at);

create table monitor_log_last_checked(
    id integer primary key,
    checked_at datetime not null,
    monitor_id int int references monitor(id) on delete cascade not null unique,
    monitor_log_id int references monitor_log(id) on delete cascade not null unique
);

create table notification_channel(
    id integer primary key,
    name text not null,
    type text not null check(type in ('smtp', 'slack')),
    details text not null
);

create table monitor_notification_channel(
    id integer primary key,
    monitor_id int references monitor(id) on delete cascade not null,
    notification_channel_id int references notification_channel(id) on delete cascade not null,
    unique(monitor_id, notification_channel_id)
);

create table mail_group(
    id integer primary key,
    name text not null,
    description text
);

create table mail_group_member(
    id integer primary key,
    email_address text not null collate nocase,
    mail_group_id int references mail_group(id) on delete cascade not null,
    unique(mail_group_id, email_address)
);

create table mail_group_monitor(
    id integer primary key,
    mail_group_id int references mail_group(id) on delete cascade not null,
    monitor_id int references monitor(id) on delete cascade not null,
    unique(mail_group_id, monitor_id)
);

insert into
    service(name, helper_text)
values
    (
        'Website',
        'Edit or delete this service in the admin area'
    );

insert into
    alert(title, type, severity, created_at)
values
    (
        'You''ve successfully deployed Statusnook 🎉',
        'maintenance',
        '',
        datetime()
    );

insert into
    alert_service(alert_id, service_id)
select
    (
        select
            id
        from
            alert
        order by
            id desc
        limit
            1
    ), (
        select
            id
        from
            service
        order by
            id desc
        limit
            1
    );

insert into
    alert_message(
        content,
        created_at,
        alert_id
    )
select
    'Go ahead and delete this alert in the admin area',
    datetime(),
    (
        select
            id
        from
            alert
        order by
            id desc
        limit
            1
    );

insert into
    alert_setting(name, value)
values
    (
        'managed-subscriptions',
        true
    );

commit;